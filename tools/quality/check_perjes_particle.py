#!/usr/bin/env python3
"""Check the exact Perjes source closure and all owned transitive axioms.

No dependency pins are changed. This is not a root-package build or a
certificate of the full analytic Penrose correspondence.
"""
from __future__ import annotations
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality.check_reviewed_prs import closure
from tools.quality.check_bilateral_kernel import audit_source, run

OWNERS = [
    'InfoGeometry.Twistor.PerjesConventions',
    'InfoGeometry.Twistor.TwistorKinematicTensor',
    'InfoGeometry.Twistor.TwistorConstituentKinematics',
    'InfoGeometry.Twistor.TwistorConstituentCCR',
    'InfoGeometry.Twistor.PerjesNullLineCorrespondence',
    'InfoGeometry.Twistor.HomogeneousTwistorCech',
    'InfoGeometry.Twistor.PenroseContourTransform',
    'InfoGeometry.Twistor.TwistorInternalSymmetry',
    'InfoGeometry.Twistor.KleinTwistorPinTransport',
]


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mathlib-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    mathlib, out = args.mathlib_root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    implemented = [m for m in OWNERS if (ROOT / 'lean' / (m.replace('.', '/') + '.lean')).is_file()]
    missing = [m for m in OWNERS if m not in implemented]
    state = dict(status='pending', targets=implemented, unimplemented=missing,
                 scope='exact source closure, not root-package build',
                 modules=[], axiom_audit_passed=False)
    try:
        pin = next(p['rev'] for p in json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
                   if p['name'] == 'mathlib')
        toolchain = (ROOT / 'lean-toolchain').read_text().strip()
        state.update(revision=run(['git', 'rev-parse', 'HEAD'], ROOT).strip(),
                     mathlib=pin, toolchain=toolchain)
        if run(['git', 'rev-parse', 'HEAD'], mathlib).strip() != pin:
            raise RuntimeError('Mathlib revision mismatch')
        if (mathlib / 'lean-toolchain').read_text().strip() != toolchain:
            raise RuntimeError('Toolchain mismatch')
        ordered, dependencies, _ = closure(ROOT, implemented)
        src, lib = out / 'src', out / 'lib'
        src.mkdir(exist_ok=True)
        lib.mkdir(exist_ok=True)
        (src / 'lean-toolchain').write_text(toolchain + '\n')
        state['source_sha256'] = {}
        for module in ordered:
            rel = Path(module.replace('.', '/') + '.lean')
            data = (ROOT / 'lean' / rel).read_bytes()
            destination = src / rel
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
            state['source_sha256'][module] = hashlib.sha256(data).hexdigest()
        with open('/tmp/info-geometry-build.lock', 'a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            processes = run(['ps', '-eo', 'comm='], ROOT).splitlines()
            if any(p.strip() in {'lean', 'lake', 'leanc'} for p in processes):
                raise RuntimeError('Concurrent compiler detected')
            (out / 'cache.log').write_text(run(['lake', 'exe', 'cache', 'get'], mathlib))
            env = os.environ.copy()
            paths = run(['lake', 'env', 'printenv', 'LEAN_PATH'], mathlib).strip().split(os.pathsep)
            env['LEAN_PATH'] = os.pathsep.join([str(lib), *[
                str((mathlib / p).resolve()) if not Path(p).is_absolute() else p for p in paths if p]])
            (out / 'lean-version.txt').write_text(run(['lean', '--version'], src, env))
            failed = set()
            for module in ordered:
                blocked = [d for d in dependencies[module] if d in failed]
                if blocked:
                    failed.add(module)
                    state['modules'].append(dict(module=module, status='blocked', dependencies=blocked))
                    print('BLOCKED', module, blocked, flush=True)
                    continue
                rel = Path(module.replace('.', '/'))
                target = (lib / rel).with_suffix('.olean')
                target.parent.mkdir(parents=True, exist_ok=True)
                result = subprocess.run(['lean', '-o', str(target), str((src / rel).with_suffix('.lean'))],
                    cwd=src, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                (out / (module + '.log')).write_text(result.stdout)
                state['modules'].append(dict(module=module, returncode=result.returncode,
                    warnings=result.stdout.count('warning:')))
                print('CHECK', module, result.returncode, flush=True)
                print(result.stdout, flush=True)
                if result.returncode:
                    failed.add(module)
            if failed:
                raise RuntimeError('Failed or blocked modules: ' + ', '.join(sorted(failed)))
            audit = src / 'PerjesParticleAudit.lean'
            audit.write_text(audit_source(implemented))
            evidence = run(['lean', str(audit)], src, env)
            (out / 'audit.log').write_text(evidence)
            if 'AUDIT_COUNT:' not in evidence:
                raise RuntimeError('Native declaration audit did not finish')
            state['axiom_audit_passed'] = True
            print(evidence, flush=True)
            if missing:
                state['status'] = 'implemented_subset_passed'
                raise RuntimeError('Planned owners not yet implemented: ' + ', '.join(missing))
            state['status'] = 'passed'
    except Exception as error:
        if state['status'] == 'pending':
            state['status'] = 'failed'
        state['error'] = str(error)
        raise
    finally:
        (out / 'status.json').write_text(json.dumps(state, indent=2) + '\n')


if __name__ == '__main__':
    main()
