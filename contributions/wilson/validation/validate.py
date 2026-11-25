#!/usr/bin/env python3
"""Validate a Wilson RG contribution against the unchanged destination project.

This runner is for an isolated CI checkout. It overlays only candidate-owned
files, records exact pins and hashes, and checks a fresh Lean axiom transcript.
It does not claim the manuscript's analytic hypotheses have been established.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

UPSTREAM_SHA = 'c25e77e9654a54fc5e4a04bfb637b7144defacc0'
CONFIG = {
    'gaussian': {
        'project': 'LEAN/Libraries/GaussianBlockSpin',
        'toolchain': 'leanprover/lean4:v4.34.0-rc2',
        'mathlib': '8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a',
        'audit': 'GaussianBlockSpin.WeightedCoarseGrainingAudit',
        'imports': ['GaussianBlockSpin.WeightedCoarseGrainingComposition',
                    'GaussianBlockSpin.WeightedEffectiveForm',
                    'GaussianBlockSpin.WeightedCoarseGrainingSpecialization',
                    'GaussianBlockSpin.WeightedKernelConvolution',
                    'GaussianBlockSpin.WeightedMarkovKernel',
                    'GaussianBlockSpin.WeightedReflectionPositive'],
        'umbrella': 'GaussianBlockSpin.lean',
    },
    'cutoff': {
        'project': 'LEAN/CoreLean',
        'toolchain': 'leanprover/lean4:v4.36.0',
        'mathlib': 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842',
        'audit': 'CoreLean.CutoffCheck',
        'imports': ['CoreLean.CutoffRecursion', 'CoreLean.CutoffLimit'],
        'umbrella': 'CoreLean.lean',
    },
    'gram': {
        'project': 'LEAN/CoreLean',
        'toolchain': 'leanprover/lean4:v4.36.0',
        'mathlib': 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842',
        'audit': 'CoreLean.PositiveKernelFiniteColimitAudit',
        'imports': ['CoreLean.PositiveKernelFiniteColimit', 'CoreLean.PositiveKernelLimit'],
        'umbrella': 'CoreLean.lean',
    },
    'states': {
        'project': 'LEAN/CoreLean',
        'toolchain': 'leanprover/lean4:v4.36.0',
        'mathlib': 'fc4f59e577feb1a4956671bc04ac18aaaf8cd842',
        'source': 'followup/states',
        'lean_prefix': 'CoreLean',
        'audit': 'CoreLean.ApproximateStateLimitsAudit',
        'imports': ['CoreLean.ApproximateCompatibility', 'CoreLean.ApproximateStateLimits'],
        'umbrella': 'CoreLean.lean',
    },
}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lean_without_comments(text: str) -> str:
    # Handle nested Lean block comments and line comments without altering code.
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                out.append('\n')
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unterminated Lean block comment')
    return ''.join(out)


def prepare(args: argparse.Namespace) -> None:
    cfg = CONFIG[args.candidate]
    target = args.upstream / cfg['project']
    revision = subprocess.check_output(
        ['git', '-C', str(args.upstream), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != UPSTREAM_SHA:
        raise SystemExit(f'Unexpected upstream revision: {revision}')
    toolchain = (target / 'lean-toolchain').read_text().strip()
    if toolchain != cfg['toolchain']:
        raise SystemExit(f'Unexpected toolchain: {toolchain}')
    pinned_files = {name: sha256(target / name)
                    for name in ('lean-toolchain', 'lakefile.lean', 'lakefile.toml', 'lake-manifest.json')
                    if (target / name).is_file()}
    source = args.source / cfg.get('source', args.candidate)
    inventory = {}
    theorem_names = []
    for path in sorted(source.rglob('*')):
        if not path.is_file():
            continue
        relative = path.relative_to(source)
        if path.suffix == '.lean' and cfg.get('lean_prefix') and relative.parts[0] != cfg['lean_prefix']:
            continue
        if args.candidate == 'gram' and path.suffix == '.lean':
            relative = Path('CoreLean') / path.name
        destination = target / relative
        if destination.exists() and destination.read_bytes() != path.read_bytes():
            raise SystemExit(f'Candidate unexpectedly replaces upstream file: {relative}')
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)
        inventory[str(relative)] = sha256(destination)
        if path.suffix == '.lean':
            code = lean_without_comments(path.read_text())
            forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', code)
            if forbidden:
                raise SystemExit(f'Forbidden proof token in {relative}: {forbidden}')
            theorem_names += re.findall(
                r'^\s*(?:@\[[^\n]*\]\s*)?(?:(?:protected|public)\s+)?'
                r'(?:theorem|lemma)\s+([^\s(:{]+)', code, flags=re.M)
    audit_path = target / Path(*cfg['audit'].split('.')).with_suffix('.lean')
    expected = re.findall(r'^#print axioms\s+(\S+)\s*$', audit_path.read_text(), re.M)
    if not expected or len(set(expected)) != len(expected):
        raise SystemExit('Axiom inventory is empty or contains duplicates')
    missing = [name for name in theorem_names
               if not any(item.rsplit('.', 1)[-1] == name for item in expected)]
    if missing:
        raise SystemExit(f'Public theorems missing from audit: {missing}')
    umbrella = target / cfg['umbrella']
    text = umbrella.read_text()
    for module in cfg['imports']:
        line = f'import {module}\n'
        if line not in text:
            text += line
    umbrella.write_text(text)
    inventory[cfg['umbrella']] = sha256(umbrella)
    args.evidence.mkdir(parents=True, exist_ok=True)
    record = {'upstream_sha': revision, 'toolchain': toolchain,
              'expected_mathlib_sha': cfg['mathlib'], 'candidate': args.candidate,
              'pinned_file_hashes': pinned_files,
              'sources': inventory, 'expected_axiom_declarations': expected,
              'public_theorem_count': len(theorem_names)}
    (args.evidence / 'source-inventory.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'candidate': args.candidate, 'files': len(inventory),
                      'theorems': len(theorem_names), 'audit_declarations': len(expected)}))


def audit(args: argparse.Namespace) -> None:
    cfg = CONFIG[args.candidate]
    target = args.upstream / cfg['project']
    inventory = json.loads((args.evidence / 'source-inventory.json').read_text())
    for relative, expected_hash in inventory['sources'].items():
        if sha256(target / relative) != expected_hash:
            raise SystemExit(f'Source changed during validation: {relative}')
    for relative, expected_hash in inventory['pinned_file_hashes'].items():
        if sha256(target / relative) != expected_hash:
            raise SystemExit(f'Destination configuration changed: {relative}')
    manifest = json.loads((target / 'lake-manifest.json').read_text())
    pin = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    if pin['rev'] != cfg['mathlib']:
        raise SystemExit(f'Mathlib pin mismatch: {pin["rev"]}')
    dependency_revisions = {}
    for package in manifest['packages']:
        if package['type'] != 'git':
            continue
        package_path = target / manifest['packagesDir'] / package['name']
        revision = subprocess.check_output(
            ['git', '-C', str(package_path), 'rev-parse', 'HEAD'], text=True).strip()
        if revision != package['rev']:
            raise SystemExit(f'Dependency HEAD mismatch: {package["name"]} {revision}')
        dependency_revisions[package['name']] = revision
    log = (args.evidence / 'axioms.log').read_text()
    matches = re.findall(
        r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        log, flags=re.S)
    actual = {}
    for declaration, axioms in matches:
        if declaration in actual:
            raise SystemExit(f'Duplicate axiom output: {declaration}')
        actual[declaration] = [a.strip() for a in axioms.split(',') if a.strip()]
    expected = set(inventory['expected_axiom_declarations'])
    if set(actual) != expected:
        raise SystemExit(f'Axiom inventory mismatch; missing={expected - set(actual)}, '
                         f'unexpected={set(actual) - expected}')
    for declaration, axioms in actual.items():
        extras = set(axioms) - ALLOWED_AXIOMS
        if extras:
            raise SystemExit(f'Unapproved axioms for {declaration}: {extras}')
    (args.evidence / 'axiom-audit.json').write_text(json.dumps(actual, indent=2) + '\n')
    (args.evidence / 'dependency-revisions.json').write_text(
        json.dumps(dependency_revisions, indent=2) + '\n')
    shutil.copyfile(target / 'lake-manifest.json', args.evidence / 'lake-manifest.json')
    print(f'PASS: {len(actual)} fresh axiom reports; destination pins and source hashes match.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['prepare', 'audit'])
    parser.add_argument('candidate', choices=CONFIG)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--upstream', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, required=True)
    args = parser.parse_args()
    {'prepare': prepare, 'audit': audit}[args.mode](args)
