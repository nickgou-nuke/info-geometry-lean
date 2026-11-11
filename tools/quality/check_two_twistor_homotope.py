#!/usr/bin/env python3
"""Compile the exact two-twistor/homotope closure and audit every new declaration.

Uses the repository's existing closure resolver, axiom collector and shared
build lock. This is scoped source verification, not a root-package build.
The supplied Mathlib checkout and its dependencies must already be hydrated.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.build_lock import acquire_build_lock
from tools.quality.check_reviewed_prs import closure
from tools.quality.check_bilateral_kernel import audit_source

OWNERS = [
    'InfoGeometry.Algebra.AssociativeHomotope',
    'InfoGeometry.Algebra.HadamardRecurrence',
    'InfoGeometry.Twistor.TwoTwistorGramMass',
    'InfoGeometry.Twistor.TwoTwistorSpinCayley',
    'InfoGeometry.Twistor.TwoTwistorInfinityBlocks',
    'InfoGeometry.Twistor.TwoTwistorUnitary',
]


def run(command, cwd, env=None, pass_fds=()):
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            pass_fds=pass_fds)
    if result.returncode:
        raise RuntimeError(f'{command!r} exited {result.returncode}\n{result.stdout}')
    return result.stdout


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mathlib-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lean', default='lean')
    args = parser.parse_args()
    mathlib, out = args.mathlib_root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    state = dict(status='pending', scope='exact repository source closure',
                 targets=OWNERS, modules=[], axiom_audit_passed=False)
    try:
        spec = json.loads((ROOT/'lake-manifest.json').read_text())
        pin = next(p['rev'] for p in spec['packages'] if p['name'] == 'mathlib')
        toolchain = (ROOT/'lean-toolchain').read_text().strip()
        state.update(revision=run(['git', 'rev-parse', 'HEAD'], ROOT).strip(),
                     mathlib=pin, toolchain=toolchain)
        if run(['git', 'rev-parse', 'HEAD'], mathlib).strip() != pin:
            raise RuntimeError('Mathlib revision differs from the repository pin')
        if (mathlib/'lean-toolchain').read_text().strip() != toolchain:
            raise RuntimeError('Mathlib toolchain differs from the repository pin')
        run(['git', 'diff', '--exit-code', 'HEAD', '--', 'Mathlib', 'Mathlib.lean'], mathlib)
        packages = [mathlib]
        dependency_pins = {}
        for dep in json.loads((mathlib/'lake-manifest.json').read_text())['packages']:
            candidates = [mathlib/'.lake/packages'/dep['name'], mathlib.parent/dep['name']]
            path = next((p for p in candidates if (p/'.git').exists()), None)
            if path is None:
                raise RuntimeError(f'Missing pinned dependency checkout: {dep["name"]}')
            actual = run(['git', 'rev-parse', 'HEAD'], path).strip()
            if actual != dep['rev']:
                raise RuntimeError(f'Dependency revision mismatch: {dep["name"]}')
            packages.append(path)
            dependency_pins[dep['name']] = actual
        state['dependency_pins'] = dependency_pins
        ordered, dependencies, _ = closure(ROOT, OWNERS)
        src, lib = out/'src', out/'lib'
        src.mkdir(); lib.mkdir()
        (src/'lean-toolchain').write_text(toolchain+'\n')
        state['source_sha256'] = {}
        for module in ordered:
            rel = Path(module.replace('.', '/')+'.lean')
            original, copied = ROOT/'lean'/rel, src/rel
            copied.parent.mkdir(parents=True, exist_ok=True)
            copied.write_bytes(original.read_bytes())
            state['source_sha256'][module] = digest(copied)
        env = os.environ.copy()
        env['LEAN_PATH'] = os.pathsep.join([str(lib), *[
            str(p/'.lake/build/lib/lean') for p in packages
            if (p/'.lake/build/lib/lean').is_dir()]])
        with acquire_build_lock(None, 'two-twistor-homotope-verification', block=True) as lock:
            descriptors = (lock.fileno(),)
            state['lean_version'] = run([args.lean, '--version'], src, env, descriptors).strip()
            version = toolchain.split(':')[-1].removeprefix('v')
            if f'version {version}' not in state['lean_version']:
                raise RuntimeError('Compiler differs from the repository toolchain')
            (out/'lean-version.txt').write_text(state['lean_version']+'\n')
            failed, warned = set(), set()
            for module in ordered:
                blocked = [d for d in dependencies[module] if d in failed]
                if blocked:
                    failed.add(module)
                    state['modules'].append(dict(module=module, status='blocked', dependencies=blocked))
                    continue
                rel = Path(module.replace('.', '/'))
                olean = (lib/rel).with_suffix('.olean')
                olean.parent.mkdir(parents=True, exist_ok=True)
                result = subprocess.run([args.lean, '-o', str(olean), str(rel.with_suffix('.lean'))],
                    cwd=src, env=env, text=True, stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT, pass_fds=descriptors)
                (out/(module+'.log')).write_text(result.stdout)
                warnings = result.stdout.count('warning:')
                state['modules'].append(dict(module=module, returncode=result.returncode, warnings=warnings))
                print('CHECK', module, result.returncode, flush=True)
                if result.stdout:
                    print(result.stdout, end='', flush=True)
                if result.returncode:
                    failed.add(module)
                if module in OWNERS and warnings:
                    warned.add(module)
            if failed:
                raise RuntimeError('Failed/blocked modules: '+', '.join(sorted(failed)))
            audit = src/'TwoTwistorHomotopeAudit.lean'
            audit.write_text(audit_source(OWNERS))
            evidence = run([args.lean, audit.name], src, env, descriptors)
            (out/'audit.log').write_text(evidence)
            if 'AUDIT_COUNT:' not in evidence:
                raise RuntimeError('Declaration audit did not finish')
            state['axiom_audit_passed'] = True
            state['audit_summary'] = [line for line in evidence.splitlines()
                                      if 'AUDIT_COUNT:' in line or 'AUDIT_AXIOMS:' in line]
            if warned:
                raise RuntimeError('Warnings in new owners: '+', '.join(sorted(warned)))
            for module, sha in state['source_sha256'].items():
                path = ROOT/'lean'/Path(module.replace('.', '/')+'.lean')
                if digest(path) != sha:
                    raise RuntimeError('Source changed during verification: '+module)
            state['status'] = 'passed'
            print('\n'.join(state['audit_summary']), flush=True)
    except Exception as error:
        state.update(status='failed', error=str(error))
        raise
    finally:
        (out/'status.json').write_text(json.dumps(state, indent=2)+'\n')


if __name__ == '__main__':
    main()
