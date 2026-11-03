#!/usr/bin/env python3
"""Replay paper endpoint modules individually, with a shared memory watchdog.

Imports are the trusted starting environment for each replay. This is not
--fresh replay of the entire dependency closure and must not be described as
such. The checker is never invoked without an exact module name.
"""
from pathlib import Path
import hashlib
import json
import os
from lean_resource_guard import run_guarded

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT
OUTPUT = ROOT / 'build/verification'


def main():
    verification = json.loads((OUTPUT / 'verification.json').read_text())
    if verification['status'] != 'PASS':
        raise ValueError('Run scripts/verify.py successfully first')
    for name, expected in verification['input_sha256'].items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected:
            raise ValueError('Stale verification: ' + name)
    from check_coverage import check
    check()
    coverage = json.loads((PROJECT / 'docs/paper-coverage.json').read_text())
    declarations = {item['name']: item['file'] for item in verification['declarations']}
    endpoints = set()
    for item in coverage['named_statements']:
        endpoints.update(item['endpoints'])
    for items in coverage['auxiliary_claims'].values():
        endpoints.update(items)
    modules = sorted({'Blotto.' + Path(declarations[name]).stem for name in endpoints})
    receipt = {'status': 'RUNNING', 'scope': 'New declarations in each listed module, relative to its imports; not fresh dependency replay.',
               'verification_sha256': hashlib.sha256((OUTPUT / 'verification.json').read_bytes()).hexdigest(),
               'replay_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'modules': modules, 'completed': []}
    path = OUTPUT / 'kernel-replay.json'
    path.write_text(json.dumps(receipt, indent=2) + '\n')
    try:
        for index, module in enumerate(modules, 1):
            print(f'Kernel replay {index}/{len(modules)}: {module}', flush=True)
            result = run_guarded(['lake', 'env', 'leanchecker', '-v', module], cwd=PROJECT,
                                 log=OUTPUT / 'replay' / (module + '.log'),
                                 timeout_seconds=600, env=dict(os.environ, LEAN_NUM_THREADS='2'))
            receipt['completed'].append({'module': module, 'resources': result})
            path.write_text(json.dumps(receipt, indent=2) + '\n')
        receipt['status'] = 'PASS'
    except BaseException as exc:
        receipt['status'] = 'FAIL'
        receipt['error'] = str(exc)
        raise
    finally:
        path.write_text(json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    main()
