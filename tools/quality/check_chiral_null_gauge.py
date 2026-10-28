#!/usr/bin/env python3
"""Check the chiral/null/gauge source closure against unchanged pinned Mathlib.

All repository imports are rebuilt serially. This is not a root Lake build.
Only public Lean.collectAxioms is used for the transitive foundation audit.
"""
from __future__ import annotations
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality.check_reviewed_prs import closure
from tools.quality.check_bilateral_kernel import audit_source, run

TARGETS = [
    'InfoGeometry.OperatorAlgebra.ChiralCouplingOperators',
    'InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport',
    'InfoGeometry.OperatorAlgebra.InnerDivergenceCharge',
    'InfoGeometry.OperatorAlgebra.ProjectiveNullInversion',
    'InfoGeometry.OperatorAlgebra.ConservedOperatorFlow',
    'InfoGeometry.OperatorAlgebra.ChiralNullGaugeTests',
]
HEADER = '''/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/'''


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mathlib-root', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    mathlib, out = args.mathlib_root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    existing = [m for m in TARGETS if (ROOT / 'lean' / (m.replace('.', '/') + '.lean')).is_file()]
    missing = sorted(set(TARGETS) - set(existing))
    state = dict(status='pending', scope='exact source closure, not root Lake build',
                 targets=TARGETS, missing=missing, modules=[], axiom_audit_passed=False)
    try:
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
        pin = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
        toolchain = (ROOT / 'lean-toolchain').read_text().strip()
        state.update(revision=run(['git', 'rev-parse', 'HEAD'], ROOT).strip(), mathlib=pin,
                     toolchain=toolchain)
        run(['git', 'diff', '--exit-code', 'HEAD', '--', 'lean'], ROOT)
        if run(['git', 'rev-parse', 'HEAD'], mathlib).strip() != pin:
            raise RuntimeError('Pinned Mathlib revision mismatch')
        if (mathlib / 'lean-toolchain').read_text().strip() != toolchain:
            raise RuntimeError('Pinned toolchain mismatch')
        ordered, dependencies, _ = closure(ROOT, existing)
        src, lib = out / 'src', out / 'lib'
        src.mkdir(exist_ok=True)
        lib.mkdir(exist_ok=True)
        (src / 'lean-toolchain').write_text(toolchain + '\n')
        state['source_sha256'] = {}
        for module in ordered:
            rel = Path(module.replace('.', '/') + '.lean')
            data = (ROOT / 'lean' / rel).read_bytes()
            target = src / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            state['source_sha256'][module] = hashlib.sha256(data).hexdigest()
            if module in existing:
                text = data.decode()
                if not text.startswith(HEADER):
                    raise RuntimeError('Missing license header: ' + module)
                if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', text):
                    raise RuntimeError('Forbidden source token: ' + module)
        with open('/tmp/info-geometry-build.lock', 'a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            if any(p.strip() in {'lean', 'lake', 'leanc'} for p in
                   run(['ps', '-eo', 'comm='], ROOT).splitlines()):
                raise RuntimeError('Concurrent compiler detected')
            (out / 'cache.log').write_text(run(['lake', 'exe', 'cache', 'get'], mathlib))
            paths = run(['lake', 'env', 'printenv', 'LEAN_PATH'], mathlib).strip().split(os.pathsep)
            env = os.environ.copy()
            env['LEAN_PATH'] = os.pathsep.join([str(lib), *[
                str((mathlib / p).resolve()) if not Path(p).is_absolute() else p for p in paths if p]])
            state['lean_version'] = run(['lean', '--version'], src, env).strip()
            failed = set()
            for module in ordered:
                blocked = [d for d in dependencies[module] if d in failed]
                if blocked:
                    failed.add(module)
                    state['modules'].append(dict(module=module, blocked=blocked))
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
            if failed or missing:
                raise RuntimeError('Failed/blocked/missing: ' + ', '.join(sorted(failed | set(missing))))
            audit = src / 'ChiralNullGaugeAudit.lean'
            audit.write_text(audit_source(TARGETS))
            evidence = run(['lean', str(audit)], src, env)
            (out / 'audit.log').write_text(evidence)
            if 'AUDIT_COUNT:' not in evidence:
                raise RuntimeError('Native declaration audit did not finish')
            state.update(status='passed', axiom_audit_passed=True,
                         audit_summary=[s for s in evidence.splitlines() if 'AUDIT_COUNT:' in s or 'AUDIT_AXIOMS:' in s])
            print(evidence, flush=True)
    except Exception as error:
        state.update(status='failed', error=str(error))
        raise
    finally:
        report = json.dumps(state, indent=2) + '\n'
        (out / 'status.json').write_text(report)
        print('CHIRAL_NULL_GAUGE_REPORT\n' + report, flush=True)


if __name__ == '__main__':
    main()
