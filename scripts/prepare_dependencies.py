#!/usr/bin/env python3
"""Resolve pinned dependencies and fetch only the required Mathlib cache closure.

Use --print-cache-roots for a read-only inventory. On an existing machine, reuse
compatible cached artifacts before running this fallback preparation script.
"""
from pathlib import Path
import json
import os
import re
import sys
from lean_resource_guard import run_guarded
from verify import without_comments

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT
OUTPUT = ROOT / 'build/verification'


def cache_roots():
    roots = set()
    for path in (PROJECT / 'Blotto').glob('*.lean'):
        for line in without_comments(path.read_text()).splitlines():
            match = re.fullmatch(r'\s*(?:(?:public|private|meta)\s+)?import\s+(?:all\s+)?([\w.\s]+)', line)
            if match:
                roots.update(name for name in match[1].split() if name.startswith('Mathlib.'))
    if not roots:
        raise ValueError('No required Mathlib cache roots found')
    return sorted(roots)


def revisions(manifest):
    return sorted((p['name'], p['url'], p['rev']) for p in manifest['packages'])


def main():
    roots = cache_roots()
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--print-cache-roots', action='store_true')
    args = parser.parse_args()
    if args.print_cache_roots:
        print('\n'.join(roots))
        return
    OUTPUT.mkdir(parents=True, exist_ok=True)
    before = revisions(json.loads((PROJECT / 'lake-manifest.json').read_text()))
    toolchain = (PROJECT / 'lean-toolchain').read_bytes()
    env = dict(os.environ, LEAN_NUM_THREADS='2', MATHLIB_NO_CACHE_ON_UPDATE='1')
    run_guarded(['lake', 'update'], cwd=PROJECT, log=OUTPUT / 'resolve-dependencies.log', env=env)
    if before != revisions(json.loads((PROJECT / 'lake-manifest.json').read_text())):
        raise ValueError('Dependency resolution changed the shipped pins; refusing cache fetch')
    if (PROJECT / 'lean-toolchain').read_bytes() != toolchain:
        raise ValueError('Dependency resolution changed the toolchain; refusing cache fetch')
    run_guarded(['lake', 'exe', 'cache', 'get', *roots], cwd=PROJECT,
                log=OUTPUT / 'fetch-required-cache.log', timeout_seconds=3600, env=env)
    print(f'Pinned dependencies ready; requested {len(roots)} Mathlib import roots')


if __name__ == '__main__':
    main()
