#!/usr/bin/env python3
"""Run one Lean job with a monitored process-group memory budget.

The monitor reads only numeric process IDs and RSS values. It refuses to start
if monitoring is unavailable, and terminates the whole job on excess memory,
timeout, or interruption. RSS is sampled, so this is a watchdog, not an OS hard
limit. Never invoke leanchecker in its default all-module parallel mode.
"""
from pathlib import Path
import fcntl
import json
import os
import re
import signal
import subprocess
import sys
import time


def process_memory():
    result = subprocess.run(
        ['ps', '-axo', 'pid=,pgid=,rss='], text=True, capture_output=True, check=True)
    return [tuple(map(int, line.split())) for line in result.stdout.splitlines() if line.strip()]


def available_memory_mb():
    if sys.platform == 'darwin':
        text = subprocess.check_output(['vm_stat'], text=True)
        size = int(re.search(r'page size of (\d+) bytes', text)[1])
        pages = sum(int(re.search(r'^' + label + r':\s+(\d+)', text, re.M)[1])
                    for label in ['Pages free', 'Pages inactive', 'Pages speculative'])
        return pages * size // (1024 * 1024)
    if sys.platform.startswith('linux'):
        text = Path('/proc/meminfo').read_text()
        return int(re.search(r'^MemAvailable:\s+(\d+)', text, re.M)[1]) // 1024
    raise RuntimeError('No system-memory monitor for this platform')


def run_guarded(command, **kwargs):
    """Serialize guarded Lean jobs in this workspace and enforce their budget."""
    lock_path = Path(__file__).resolve().parents[1] / 'build/verification/.resource-guard.lock'
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open('a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise RuntimeError('Another guarded Lean job is already running') from exc
        return _run_guarded(command, **kwargs)


def _run_guarded(command, *, cwd, log, max_rss_mb=6144, timeout_seconds=3600, env=None,
                 min_available_mb=4096):
    """Return an execution receipt; fail closed if the job cannot be monitored."""
    if max_rss_mb <= 0 or timeout_seconds <= 0:
        raise ValueError('Memory and time budgets must be positive')
    # Check permission before launching any potentially expensive process.
    process_memory()
    if available_memory_mb() < max_rss_mb + min_available_mb:
        raise RuntimeError('Insufficient memory headroom to start the Lean job')
    started = time.monotonic()
    peak = 0
    status = 'FAIL'
    reason = None
    child = None
    log = Path(log)
    log.parent.mkdir(parents=True, exist_ok=True)
    try:
        with log.open('w') as stream:
            child = subprocess.Popen(command, cwd=cwd, env=env,
                                     stdout=stream, stderr=subprocess.STDOUT,
                                     start_new_session=True)
            while True:
                rss = sum(rss for _, group, rss in process_memory() if group == child.pid)
                peak = max(peak, rss)
                if rss > max_rss_mb * 1024:
                    reason = 'Process-group RSS exceeded memory budget'
                    raise RuntimeError(reason)
                if available_memory_mb() < min_available_mb:
                    reason = 'System memory headroom fell below reserve'
                    raise RuntimeError(reason)
                if time.monotonic() - started > timeout_seconds:
                    reason = 'Execution exceeded time budget'
                    raise RuntimeError(reason)
                code = child.poll()
                if code is not None:
                    if code:
                        reason = f'Command exited with status {code}'
                        raise RuntimeError(reason)
                    status = 'PASS'
                    break
                time.sleep(0.25)
    except BaseException as exc:
        reason = reason or str(exc) or type(exc).__name__
        raise
    finally:
        if child is not None and status != 'PASS':
            # Include descendants even if the original parent has just exited.
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                child.wait(timeout=2)
            except subprocess.TimeoutExpired:
                pass
            # Do not signal an already empty/reaped group (macOS can report
            # EPERM instead of ESRCH for that case).
            if any(group == child.pid and rss > 0 for _, group, rss in process_memory()):
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            child.wait()
        receipt = {'status': status, 'command': command, 'max_rss_mb': max_rss_mb,
                   'peak_sampled_rss_mb': round(peak / 1024, 2),
                   'timeout_seconds': timeout_seconds,
                   'elapsed_seconds': round(time.monotonic() - started, 3),
                   'reason': reason, 'sampling_seconds': 0.25}
        receipt['min_available_mb'] = min_available_mb
        log.with_suffix(log.suffix + '.resources.json').write_text(json.dumps(receipt, indent=2) + '\n')
    return receipt
