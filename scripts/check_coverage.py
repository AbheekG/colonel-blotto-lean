#!/usr/bin/env python3
"""Check the paper endpoint map against the current verified source inventory."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'build/verification'


def check():
    path = OUTPUT / 'verification.json'
    verification = json.loads(path.read_text())
    if verification['status'] != 'PASS':
        raise ValueError('Run scripts/verify.py successfully first')
    for name, expected in verification['input_sha256'].items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected:
            raise ValueError('Verification source changed: ' + name)
    mapping = json.loads((ROOT / 'docs/paper-coverage.json').read_text())
    labels = [item['label'] for item in mapping['named_statements']]
    if len(labels) != mapping['named_statement_count'] or len(labels) != len(set(labels)):
        raise ValueError('Duplicate or missing named paper statement')
    declarations = {item['name'] for item in verification['declarations']}
    groups = {item['label']: item['endpoints'] for item in mapping['named_statements']}
    groups.update(mapping['auxiliary_claims'])
    groups.update(mapping['definitions'])
    for label, endpoints in groups.items():
        if not endpoints or not set(endpoints).issubset(declarations):
            raise ValueError('Missing formal endpoint for ' + label)
    result = {'status': 'PASS', 'named_statements': len(labels),
              'auxiliary_groups': len(mapping['auxiliary_claims']),
              'definition_groups': len(mapping['definitions']),
              'verification_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
              'mapping_sha256': hashlib.sha256((ROOT / 'docs/paper-coverage.json').read_bytes()).hexdigest(),
              'scope': 'Endpoint existence in checked source; English correspondence was reviewed separately.'}
    (OUTPUT / 'coverage.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    argparse.ArgumentParser(description=__doc__).parse_args()
    print(json.dumps(check(), indent=2))
