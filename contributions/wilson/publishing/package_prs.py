#!/usr/bin/env python3
"""Prepare independent upstream branches and reviewable Git patches.

Only task-owned refs are changed. The upstream checkout, its index, and its
working tree remain untouched. No network write or PR publication occurs here.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
CANDIDATES = HERE.parent
SOURCE_REPOSITORY = HERE.parents[2]
DEFAULT_UPSTREAM = SOURCE_REPOSITORY.parent / '4D_Wilson_Loop_RG'
BASE = 'c25e77e9654a54fc5e4a04bfb637b7144defacc0'
SPECS = {
    'gaussian': {
        'project': 'LEAN/Libraries/GaussianBlockSpin',
        'branch': 'codex/weighted-gaussian-coarse-graining-20261124',
        'title': 'Add matrix-weighted Gaussian coarse-graining and native Markov kernels',
        'workflow': 'weighted-gaussian.yml',
        'readme': 'README-weighted-coarse-graining.md',
        'umbrella': 'GaussianBlockSpin.lean',
        'imports': ['GaussianBlockSpin.WeightedCoarseGrainingComposition',
                    'GaussianBlockSpin.WeightedEffectiveForm',
                    'GaussianBlockSpin.WeightedCoarseGrainingSpecialization',
                    'GaussianBlockSpin.WeightedKernelConvolution',
                    'GaussianBlockSpin.WeightedMarkovKernel',
                    'GaussianBlockSpin.WeightedReflectionPositive'],
    },
    'cutoff': {
        'project': 'LEAN/CoreLean',
        'branch': 'codex/cutoff-comparison-summability-20261124',
        'title': 'Add normalized cutoff estimates and real power-log summability',
        'workflow': 'cutoff-comparison.yml',
        'readme': 'README-cutoff-comparison.md',
        'umbrella': 'CoreLean.lean',
        'imports': ['CoreLean.CutoffRecursion', 'CoreLean.CutoffLimit'],
    },
    'gram': {
        'project': 'LEAN/CoreLean',
        'branch': 'codex/positive-kernel-hilbert-colimit-20261124',
        'title': 'Construct complex finite Gram quotients and their Hilbert colimit',
        'workflow': 'positive-kernel-colimit.yml',
        'readme': 'README-positive-kernel-colimit.md',
        'umbrella': 'CoreLean.lean',
        'imports': ['CoreLean.PositiveKernelFiniteColimit', 'CoreLean.PositiveKernelLimit'],
    },
    'states': {
        'project': 'LEAN/CoreLean',
        'source': 'followup/states',
        'lean_prefix': 'CoreLean',
        'branch': 'codex/approximate-compatible-states-20261124',
        'title': 'Construct positive compatible limits from summable state errors',
        'workflow': 'approximate-state-limits.yml',
        'readme': 'README-approximate-state-limits.md',
        'umbrella': 'CoreLean.lean',
        'imports': ['CoreLean.ApproximateCompatibility', 'CoreLean.ApproximateStateLimits'],
    },
}


def git(upstream: Path, *args: str, input: bytes | None = None,
        env=None, check=True) -> subprocess.CompletedProcess:
    return subprocess.run(['git', '-C', str(upstream), *args], input=input,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          env=env, check=check)


def text_git(upstream: Path, *args: str, **kwargs) -> str:
    return git(upstream, *args, **kwargs).stdout.decode().strip()


def main(upstream: Path) -> None:
    if text_git(upstream, 'rev-parse', 'HEAD') != BASE or text_git(upstream, 'status', '--short'):
        raise SystemExit('Upstream checkout changed; inspect it before packaging.')
    checkpoint = HERE / 'prepared-prs.json'
    previous = json.loads(checkpoint.read_text()) if checkpoint.exists() else {}
    record = {'upstream_repository': 'MathePhysics/4D_Wilson_Loop_RG',
              'upstream_base': BASE, 'publication_status': 'requires writable fork',
              'prs': {}}
    for key, spec in SPECS.items():
        source = CANDIDATES / spec.get('source', key)
        changes: dict[str, bytes] = {}
        for path in sorted(source.rglob('*')):
            if not path.is_file() or not (
                    path.suffix in ('.lean', '.md') or path.name.startswith('LICENSE')):
                continue
            relative = path.relative_to(source)
            if path.suffix == '.lean' and spec.get('lean_prefix') and relative.parts[0] != spec['lean_prefix']:
                continue
            if relative.name == 'THEOREM_CONTRACT.md':
                relative = Path(spec['readme'])
            changes[str(Path(spec['project']) / relative)] = path.read_bytes()
        umbrella = str(Path(spec['project']) / spec['umbrella'])
        original = git(upstream, 'show', f'{BASE}:{umbrella}').stdout.decode()
        for module in spec['imports']:
            line = f'import {module}\n'
            if line not in original:
                original += line
        changes[umbrella] = original.encode()
        for relative in ('.github/scripts/check_lean_axioms.py',
                         '.github/workflows/' + spec['workflow']):
            changes[relative] = (HERE / relative).read_bytes()
        ref = 'refs/heads/' + spec['branch']
        existing = git(upstream, 'rev-parse', '--verify', ref, check=False)
        old = existing.stdout.decode().strip() if existing.returncode == 0 else None
        known = previous.get('prs', {}).get(key, {}).get('local_commit')
        if old and old != known:
            raise SystemExit(f'Ref {ref} is not at our recorded checkpoint; inspect before updating.')
        with tempfile.TemporaryDirectory(prefix='wilson-pr-index-') as temporary:
            env = dict(os.environ, GIT_INDEX_FILE=str(Path(temporary) / 'index'))
            git(upstream, 'read-tree', BASE, env=env)
            for relative, content in changes.items():
                blob = text_git(upstream, 'hash-object', '-w', '--stdin', input=content)
                git(upstream, 'update-index', '--add', '--cacheinfo', f'100644,{blob},{relative}', env=env)
            tree = text_git(upstream, 'write-tree', env=env)
        if old and text_git(upstream, 'rev-parse', old + '^{tree}') == tree:
            commit = old
        else:
            message = spec['title'] + '\n\nPrepared upstream contribution; see its theorem contract and focused audit.\n'
            commit = text_git(upstream, 'commit-tree', tree, '-p', BASE, input=message.encode())
            git(upstream, 'update-ref', ref, commit, old or '0' * 40)
        git(upstream, 'diff', '--check', BASE, commit)
        patch = HERE / 'patches' / (key + '.patch')
        patch.parent.mkdir(exist_ok=True)
        patch.write_bytes(git(upstream, 'format-patch', '--stdout', '-1', commit).stdout)
        entries = [{'path': name, 'mode': '100644', 'type': 'blob',
                    'content': content.decode()} for name, content in changes.items()]
        (HERE / (key + '-tree.json')).write_text(json.dumps(entries, indent=2) + '\n')
        record['prs'][key] = {
            **spec, 'local_commit': commit, 'tree': tree, 'patch': str(patch.relative_to(HERE)),
            'description': 'descriptions/' + key + '.md',
            'files': {name: hashlib.sha256(content).hexdigest() for name, content in changes.items()},
            'patch_sha256': hashlib.sha256(patch.read_bytes()).hexdigest(),
        }
        print(json.dumps({'candidate': key, 'branch': spec['branch'], 'commit': commit,
                          'files': len(changes), 'patch': str(patch)}))
    checkpoint.write_text(json.dumps(record, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', type=Path, default=DEFAULT_UPSTREAM,
                        help='Clean destination checkout at the pinned base '
                             '(default: 4D_Wilson_Loop_RG beside the source repository)')
    args = parser.parse_args()
    main(args.upstream.resolve())
