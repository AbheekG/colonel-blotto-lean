#!/usr/bin/env python3
"""Build all Blotto modules and audit their declarations and axioms.

The kernel checks declarations when their modules are built. The compiled
environment is inspected at trust zero, including private and generated safe
declarations. Lean-generated _unsafe_rec implementations are reported separately.
Imported .olean proofs are not re-typechecked by this audit. The pinned toolchain
provides leanchecker for selective replay; its default parallel mode is unsafe
for this large project. This checks formal statements, not their English meaning.
Coverage and outstanding obligations are recorded in docs/verification.md.
All generated files and logs stay in build/verification/.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import time
import tomllib
from lean_resource_guard import run_guarded

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT
OUTPUT = ROOT / 'build' / 'verification'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def without_comments(source):
    """Remove Lean's nested block comments, line comments, and string contents."""
    result = []
    depth = 0
    quoted = False
    i = 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1
                i += 2
            elif source.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                result.append('\n' if source[i] == '\n' else ' ')
                i += 1
        elif quoted:
            if source[i] == '\\':
                i += 2
            elif source[i] == '"':
                quoted = False
                i += 1
            else:
                result.append('\n' if source[i] == '\n' else ' ')
                i += 1
        elif source.startswith('/-', i):
            depth = 1
            result.append(' ')
            i += 2
        elif source.startswith('--', i):
            newline = source.find('\n', i)
            i = len(source) if newline == -1 else newline
        elif source[i] == '"':
            quoted = True
            i += 1
        else:
            result.append(source[i])
            i += 1
    if depth or quoted:
        raise ValueError('Unclosed comment or string')
    return ''.join(result)


def declarations(path):
    code = without_comments(path.read_text())
    if re.search(r'\b(sorry|admit|sorryAx|axiom|unsafe|partial|native_decide|implemented_by|extern)\b', code):
        raise ValueError('Forbidden proof escape or axiom in ' + str(path))
    scopes = []
    found = []
    for line_number, line in enumerate(code.splitlines(), 1):
        # Lean permits indented top-level declarations and namespace commands.
        line = line.lstrip()
        match = re.match(r'^namespace\s+([\w.]+)', line)
        if match:
            scopes.append(match[1])
            continue
        if re.match(r'^end(?:\s|$)', line):
            if not scopes:
                raise ValueError('Unsupported end/section in ' + str(path))
            scopes.pop()
            continue
        match = re.match(r'^(?:noncomputable\s+)?(?:@\[.*\]\s+)?'
                         r'(theorem|lemma|def|abbrev|structure|inductive)\s+([\w.]+)', line)
        if match:
            found.append({'name': '.'.join(scopes + [match[2]]),
                          'kind': match[1], 'line': line_number,
                          'file': str(path.relative_to(ROOT))})
    if scopes:
        raise ValueError('Unclosed namespace in ' + str(path))
    return found


def run(command, log_name):
    log = OUTPUT / log_name
    run_guarded(command, cwd=PROJECT, log=log,
                env=dict(os.environ, LEAN_NUM_THREADS='1' if 'build' in command else '2'))
    text = log.read_text()
    if re.search(r'(^|\n)(?:.*: )?error:', text) or 'PANIC' in text:
        print(text[-12000:], file=sys.stderr)
        raise RuntimeError('Verification command failed; see ' + str(log))
    return text


def check_versions():
    """Check portable pins against the effective compiler and dependency checkouts."""
    toolchain = (PROJECT / 'lean-toolchain').read_text().strip()
    target = re.fullmatch(r'leanprover/lean4:v(\d+\.\d+\.\d+)', toolchain)
    if not target:
        raise ValueError('Expected an exact stable Lean toolchain pin')
    config = tomllib.loads((PROJECT / 'lakefile.toml').read_text())
    manifest = json.loads((PROJECT / 'lake-manifest.json').read_text())
    packages = {p['name']: p for p in manifest['packages']}
    for requirement in config.get('require', []):
        name = requirement['name']
        revision = requirement.get('rev', '')
        if not requirement.get('git') or not re.fullmatch(r'[0-9a-f]{40}', revision):
            raise ValueError('Expected an exact portable Git pin for ' + name)
        package = packages.get(name, {})
        if (package.get('rev') != revision or package.get('inputRev') != revision
                or package.get('url') != requirement['git']):
            raise ValueError('Direct dependency does not match its manifest: ' + name)
    version = run(['lake', 'env', 'lean', '--version'], 'lean-version.log').strip()
    if not re.search(r'\bversion ' + re.escape(target[1]) + r'[,)]', version):
        raise ValueError('Effective compiler differs from lean-toolchain: ' + version)
    compiler_revision = run(['lake', 'env', 'lean', '--githash'], 'lean-revision.log').strip()
    revisions = {}
    packages_dir = PROJECT / manifest['packagesDir']
    for name, package in packages.items():
        if package.get('type') != 'git' or not re.fullmatch(r'[0-9a-f]{40}', package.get('rev', '')):
            raise ValueError('Expected a resolved exact Git revision for ' + name)
        checkout = (packages_dir / name).resolve()
        if not checkout.is_relative_to(ROOT):
            raise ValueError('Dependency escaped the isolated/project workspace: ' + name)
        head = subprocess.check_output(['git', '-C', str(checkout), 'rev-parse', 'HEAD'], text=True).strip()
        if head != package['rev']:
            raise ValueError('Dependency checkout differs from its manifest: ' + name)
        dirty = subprocess.check_output(
            ['git', '-C', str(checkout), 'status', '--porcelain', '--untracked-files=normal'], text=True)
        if dirty:
            raise ValueError('Dependency checkout has local changes: ' + name)
        revisions[name] = head
    mathlib_toolchain = (packages_dir / 'mathlib' / 'lean-toolchain').read_text().strip()
    if mathlib_toolchain != toolchain:
        raise ValueError('Mathlib toolchain differs from the project toolchain')
    return {'toolchain': toolchain, 'lean_version': version, 'lean_revision': compiler_revision,
            'mathlib_toolchain': mathlib_toolchain, 'dependency_revisions': revisions}


def main():
    started = time.monotonic()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    packages = PROJECT / json.loads((PROJECT / 'lake-manifest.json').read_text())['packagesDir']
    if not (packages / 'mathlib').is_dir():
        raise ValueError('Run python3 scripts/prepare_dependencies.py first')
    versions = check_versions()
    sources = sorted((PROJECT / 'Blotto').glob('*.lean'))
    imports = re.findall(r'^import Blotto\.(\w+)\s*$', (PROJECT / 'Blotto.lean').read_text(), re.M)
    if len(imports) != len(set(imports)) or set(imports) != {p.stem for p in sources}:
        raise ValueError('Blotto.lean must import every maintained module exactly once')
    extra_sources = set(PROJECT.rglob('*.lean')) - set(sources) - {PROJECT / 'Blotto.lean'}
    extra_sources = {p for p in extra_sources if '.lake' not in p.parts and 'build' not in p.relative_to(ROOT).parts}
    extra_sources.discard(Path(__file__).with_name('LeanEnvironmentAudit.lean'))
    if extra_sources:
        raise ValueError('Unaccounted Lean sources: ' + str(sorted(extra_sources)))
    inputs = sources + [PROJECT / 'Blotto.lean', PROJECT / 'lakefile.toml',
                        PROJECT / 'lean-toolchain', PROJECT / 'lake-manifest.json',
                        Path(__file__).resolve(), Path(__file__).with_name('lean_resource_guard.py'),
                        Path(__file__).with_name('LeanEnvironmentAudit.lean')]
    input_hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    (OUTPUT / 'verification.json').write_text(json.dumps({'status': 'RUNNING', 'input_sha256': input_hashes}) + '\n')
    records = [entry for path in sources for entry in declarations(path)]
    names = [entry['name'] for entry in records]
    if len(set(names)) != len(names):
        raise ValueError('Duplicate declaration name')
    print('Building the Lean project...', flush=True)
    # Explicit targets prevent a stale omitted-module olean from passing the audit.
    run(['lake', 'build', 'Blotto', *('Blotto.' + p.stem for p in sources)], 'verify-build.log')
    print('Auditing all compiled declarations, including private and generated helpers...', flush=True)
    inventory = run(['lake', 'env', 'lean', '-j2', '-t', '0',
                     str(Path(__file__).with_name('LeanEnvironmentAudit.lean'))], 'environment-audit.log')
    match = re.search(r'^ENVIRONMENT_AUDIT (\{.*\})$', inventory, re.M)
    if not match:
        raise ValueError('Compiled environment inventory did not produce its receipt')
    summary = json.loads(match[1])
    if summary['modules'] != len(sources):
        raise ValueError('Compiled environment inventory did not cover all maintained modules')
    if not set(names).issubset(summary['names']):
        raise ValueError('Source declarations missing from the compiled environment')
    axioms = set(summary['axioms'])
    if axioms - ALLOWED_AXIOMS:
        raise ValueError('Unapproved axioms in compiled environment')
    if input_hashes != {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}:
        raise ValueError('Verification inputs changed during the audit')
    receipt = {
        'status': 'PASS', 'module_count': len(sources),
        'theorem_count': sum(r['kind'] in {'theorem', 'lemma'} for r in records),
        'audited_declaration_count': len(records), 'axioms': sorted(axioms),
        'sorry_count': 0, 'custom_axiom_count': 0, 'trust_level': 0,
        'elapsed_seconds': round(time.monotonic() - started, 3),
        **versions,
        'input_sha256': input_hashes,
        'declarations': records,
        'environment_audit': {key: value for key, value in summary.items() if key != 'names'},
        'kernel_replay': 'Not implied by this receipt: imported oleans are not re-typechecked by lean -t 0.',
        'resource_usage': {
            name: {key: value for key, value in json.loads((OUTPUT / (name + '.resources.json')).read_text()).items()
                   if key != 'command'}
            for name in ['lean-version.log', 'lean-revision.log', 'verify-build.log', 'environment-audit.log']},
        'scope': 'Checks exact Lean statements, source inventory, axioms and pins. '
                 'English correspondence is reviewed separately. Cost theorems concern '
                 'defined operation prices/work functions; full execution correspondence remains open.'
    }
    (OUTPUT / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in ['status', 'module_count', 'theorem_count',
          'audited_declaration_count', 'axioms', 'trust_level', 'elapsed_seconds']}, indent=2))


if __name__ == '__main__':
    import argparse
    argparse.ArgumentParser(description=__doc__).parse_args()
    try:
        main()
    except BaseException as exc:
        OUTPUT.mkdir(parents=True, exist_ok=True)
        (OUTPUT / 'verification.json').write_text(json.dumps({'status': 'FAIL', 'error': str(exc)}) + '\n')
        raise
