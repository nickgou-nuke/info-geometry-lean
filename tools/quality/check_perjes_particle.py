#!/usr/bin/env python3
"""Verify exact Perjes/Klein source closure with pinned Lean and Mathlib.

This does not modify dependency pins or claim a root-package build. Every
changed mathematical owner and the aggregate are compiled. The native
Lean.collectAxioms audit checks all declarations in the changed owners.
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

OWNERS = ['InfoGeometry.Twistor.PerjesConventions', 'InfoGeometry.Twistor.TwistorKinematicTensor', 'InfoGeometry.Twistor.TwistorConstituentKinematics', 'InfoGeometry.Twistor.TwistorConstituentCCR', 'InfoGeometry.Twistor.PerjesNullLineCorrespondence', 'InfoGeometry.Twistor.HomogeneousTwistorCech', 'InfoGeometry.Twistor.PenroseContourTransform', 'InfoGeometry.Twistor.TwistorInternalSymmetry', 'InfoGeometry.Twistor.KleinTwistorPinTransport', 'InfoGeometry.Physics.Pin55Glide', 'InfoGeometry.Topology.KleinBottleSpinorGlide', 'InfoGeometry.Twistor.ConstituentColumnEquivalence', 'InfoGeometry.Twistor.ConstituentLinearStabilizer', 'InfoGeometry.Twistor.ConstituentMomentumTransport', 'InfoGeometry.Twistor.ConstituentPolynomialEmbedding', 'InfoGeometry.Twistor.PerjesIncidencePairing', 'InfoGeometry.Twistor.PerjesMomentOperator']
ENTRY = 'InfoGeometry.Twistor.PerjesParticleGeometry'


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mathlib-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    mathlib, out = args.mathlib_root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    state = dict(status='pending', targets=OWNERS + [ENTRY],
                 scope='exact source closure, not root-package build',
                 modules=[], axiom_audit_passed=False, source_matches_commit=False)
    try:
        pin = next(p['rev'] for p in json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
                   if p['name'] == 'mathlib')
        toolchain = (ROOT / 'lean-toolchain').read_text().strip()
        state.update(revision=run(['git', 'rev-parse', 'HEAD'], ROOT).strip(),
                     mathlib=pin, toolchain=toolchain)
        run(['git', 'diff', '--exit-code', 'HEAD', '--', 'lean'], ROOT)
        state['source_matches_commit'] = True
        if run(['git', 'rev-parse', 'HEAD'], mathlib).strip() != pin:
            raise RuntimeError('Mathlib revision mismatch')
        if (mathlib / 'lean-toolchain').read_text().strip() != toolchain:
            raise RuntimeError('Toolchain mismatch')
        ordered, dependencies, _ = closure(ROOT, OWNERS + [ENTRY])
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
            state['lean_version'] = run(['lean', '--version'], src, env).strip()
            (out / 'lean-version.txt').write_text(state['lean_version'] + '\n')
            failed, warning_owners = set(), set()
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
                warnings = result.stdout.count('warning:')
                state['modules'].append(dict(module=module, returncode=result.returncode, warnings=warnings))
                print('CHECK', module, result.returncode, flush=True)
                print(result.stdout, flush=True)
                if result.returncode:
                    failed.add(module)
                if module in OWNERS and warnings:
                    warning_owners.add(module)
            if failed:
                raise RuntimeError('Failed or blocked modules: ' + ', '.join(sorted(failed)))
            state['kernel_closure_passed'] = True
            audit = src / 'PerjesParticleAudit.lean'
            audit.write_text(audit_source(OWNERS))
            evidence = run(['lean', str(audit)], src, env)
            (out / 'audit.log').write_text(evidence)
            if 'AUDIT_COUNT:' not in evidence:
                raise RuntimeError('Native declaration audit did not finish')
            state['axiom_audit_passed'] = True
            state['audit_summary'] = [line for line in evidence.splitlines() if 'AUDIT_COUNT:' in line]
            print(evidence, flush=True)
            if warning_owners:
                raise RuntimeError('Warnings in changed owners: ' + ', '.join(sorted(warning_owners)))
            state['status'] = 'passed'
    except Exception as error:
        state['status'] = 'failed'
        state['error'] = str(error)
        raise
    finally:
        report = json.dumps(state, indent=2) + '\n'
        (out / 'status.json').write_text(report)
        print('PERJES_VERIFICATION_REPORT\n' + report, flush=True)


if __name__ == '__main__':
    main()
