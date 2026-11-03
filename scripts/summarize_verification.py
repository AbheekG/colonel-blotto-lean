#!/usr/bin/env python3
"""Write a compact public summary of the current full verification receipts."""
from pathlib import Path
import argparse
import hashlib
import json
from check_coverage import check

ROOT = Path(__file__).resolve().parents[1]


def main():
    coverage = check()
    verification_path = ROOT / 'build/verification/verification.json'
    verification = json.loads(verification_path.read_text())
    replay = json.loads((ROOT / 'build/verification/kernel-replay.json').read_text())
    if replay['status'] != 'PASS' or replay['verification_sha256'] != hashlib.sha256(verification_path.read_bytes()).hexdigest():
        raise ValueError('No complete current endpoint replay')
    if set(replay['modules']) != {item['module'] for item in replay['completed']}:
        raise ValueError('Incomplete endpoint replay')
    inputs = verification['input_sha256']
    fingerprint = hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    env = verification['environment_audit']
    summary = {'status': 'PASS', 'schema_version': 1,
               'source_and_checker_fingerprint': fingerprint,
               'lean_toolchain': verification['toolchain'], 'lean_revision': verification['lean_revision'],
               'dependency_revisions': verification['dependency_revisions'],
               'module_count': verification['module_count'],
               'source_named_theorem_count': verification['theorem_count'],
               'compiled_declaration_count': env['declarations'],
               'compiled_theorem_count': env['theorems'],
               'private_declaration_count': env['private_declarations'],
               'compiler_recursion_helpers_recorded_separately': len(env['compiler_unsafe_rec_helpers']),
               'allowed_axioms': verification['axioms'],
               'named_paper_statements': coverage['named_statements'],
               'replayed_endpoint_modules': len(replay['completed']),
               'scope': 'All-module build and safe-declaration axiom audit; endpoint module replay relative to imports. Full execution/cost correspondence remains open.'}
    path = ROOT / 'docs/verification-baseline.json'
    path.write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    argparse.ArgumentParser(description=__doc__).parse_args()
    main()
