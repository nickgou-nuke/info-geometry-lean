#!/usr/bin/env python3
"""Check the Peirce superoperator source closure and every new declaration's axioms.

Uses the repository's pinned, already initialized Mathlib without changing its
sources or metadata. Output is isolated from the repository and dependency caches.
This is a scoped source-closure check, not an exhaustive repository Lake build.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.build_lock import BuildLock, DEFAULT_BUILD_LOCK_PATH
from tools.quality.check_reviewed_prs import closure
from tools.quality.reviewed_audit_source import audit_source, parse_audit_output, validate_targets

PREFIX = 'InfoGeometry.OperatorAlgebra.PeirceSuperoperators'
INTRINSIC = 'InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint'
INTRINSIC_SOURCE_SHA256 = '77610dd9f8583cb5ebae047f65a4351ef4bbdaabab387d64d0efd861d7c5316c'
TARGETS = [INTRINSIC] + [f'{PREFIX}.{name}' for name in
    ('MixedActions', 'SquareZeroPair', 'PeirceParity', 'PeirceDifferential',
     'HilbertSchmidt', 'HodgeKernel', 'MatrixParity', 'Examples',
     'Crossover', 'TraceAdjoint', 'StationaryAlgebra', 'DoubleCommutator',
     'SkewPerturbation', 'CrossoverExamples')]


def owned(module):
    return module == INTRINSIC or module.startswith(PREFIX)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, cwd, env=None, pass_fds=()):
    result = subprocess.run(command, cwd=cwd, env=env, pass_fds=pass_fds,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'{command!r} exited {result.returncode}\n{result.stdout}')
    return result.stdout.strip()


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mathlib-root', type=Path, required=True)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--target', action='append')
    parser.add_argument('--incremental', action='store_true')
    parser.add_argument('--skip-audit', action='store_true', help='Development only; never acceptance')
    args = parser.parse_args()
    targets = validate_targets(args.target or TARGETS)
    mathlib, out = args.mathlib_root.resolve(), args.output.resolve()
    lean = shutil.which(args.lean)
    if lean is None:
        raise RuntimeError('Pinned Lean executable not found')
    out.mkdir(parents=True, exist_ok=True)
    report_path = out / 'report.json'
    previous = json.loads(report_path.read_text()) if args.incremental and report_path.exists() else {}
    report = {'status': 'pending', 'scope': 'Exact repository source closure and native axiom audit',
              'targets': targets, 'modules': [], 'audit_required': not args.skip_audit,
              'target_override': args.target, 'incremental': args.incremental,
              'skip_audit': args.skip_audit}
    helpers = ['tools/quality/check_peirce_superoperators.py', 'tools/quality/check_reviewed_prs.py',
               'tools/quality/reviewed_audit_source.py', 'tools/build_lock.py',
               'tools/quality/semantic_vacuity_gate.py', 'tools/quality/semantic_vacuity_patterns.json',
               'tools/quality/placeholder_audit.py', '.githooks/pre-commit',
               'tools/quality/proof_proxy_staged_gate.py', 'tools/infra/opengauss_screener.py',
               'lean/InfoGeometry/OperatorAlgebra/All.lean',
               'lean-toolchain', 'lake-manifest.json',
               '.github/workflows/peirce-superoperators.yml',
               'docs/PEIRCE_SUPEROPERATOR_CONTRACT.md',
               'docs/PEIRCE_TRACE_CROSSOVER_CONTRACT.md']
    helper_hashes = {p: digest(ROOT / p) for p in helpers}
    report['verification_source_sha256'] = helper_hashes
    try:
        intrinsic_path = ROOT / 'lean' / (INTRINSIC.replace('.', '/') + '.lean')
        if digest(intrinsic_path) != INTRINSIC_SOURCE_SHA256:
            raise RuntimeError('Reused canonical graded owner differs from the reviewed original source')
        report['reused_owner_sha256'] = {INTRINSIC: INTRINSIC_SOURCE_SHA256}
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
        pin = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
        toolchain = (ROOT / 'lean-toolchain').read_text().strip()
        if run(['git', 'rev-parse', 'HEAD'], mathlib) != pin:
            raise RuntimeError('Mathlib revision differs from the repository pin')
        if (mathlib / 'lean-toolchain').read_text().strip() != toolchain:
            raise RuntimeError('Mathlib toolchain differs from the repository pin')
        run(['git', 'diff', '--exit-code', 'HEAD', '--'], mathlib)
        roots = targets + ([PREFIX] if args.target is None else [])
        ordered, dependencies, _ = closure(ROOT, roots)
        source, lib = out / 'src', out / 'lib'
        source.mkdir(exist_ok=True)
        lib.mkdir(exist_ok=True)
        (source / 'lean-toolchain').write_text(toolchain + '\n')
        hashes, fingerprints = {}, {}
        for module in ordered:
            rel = Path(module.replace('.', '/') + '.lean')
            original, copied = ROOT / 'lean' / rel, source / rel
            copied.parent.mkdir(parents=True, exist_ok=True)
            data = original.read_bytes()
            copied.write_bytes(data)
            hashes[module] = hashlib.sha256(data).hexdigest()
            if digest(original) != hashes[module]:
                raise RuntimeError('Source changed while copying: ' + module)
            payload = [module, hashes[module], pin, toolchain,
                       [fingerprints[d] for d in dependencies[module]]]
            fingerprints[module] = hashlib.sha256(json.dumps(payload).encode()).hexdigest()
        if INTRINSIC in hashes and hashes[INTRINSIC] != INTRINSIC_SOURCE_SHA256:
            raise RuntimeError('Copied canonical graded owner differs from the reviewed original source')
        report.update(mathlib=pin, toolchain=toolchain, source_sha256=hashes,
                      fingerprints=fingerprints,
                      repository_import_dependencies=dependencies,
                      local_revision=run(['git', 'rev-parse', 'HEAD'], ROOT))
        print('Waiting for shared build lock', flush=True)
        with BuildLock(DEFAULT_BUILD_LOCK_PATH, 'peirce-superoperators', block=True) as lock:
            pass_fds = (lock.fileno(),)
            active = run(['ps', '-eo', 'comm='], ROOT, pass_fds=pass_fds).splitlines()
            if any(p.strip() in {'lean', 'lake', 'leanc'} for p in active):
                raise RuntimeError('Concurrent Lean compiler detected')
            version = run([lean, '--version'], source, pass_fds=pass_fds)
            actual_version = re.search(r'\bversion ([^, ]+)', version)
            if actual_version is None or actual_version.group(1) != toolchain.rsplit(':v', 1)[-1]:
                raise RuntimeError('Lean executable does not match the pinned version')
            report['lean_version'] = version
            prefix = Path(run([lean, '--print-prefix'], source, pass_fds=pass_fds))
            packages = sorted((mathlib / '.lake/packages').glob('*/.lake/build/lib/lean'))
            search = [lib, *packages, mathlib / '.lake/build/lib/lean', prefix / 'lib/lean']
            env = {**os.environ, 'LEAN_PATH': os.pathsep.join(map(str, search))}
            (out / 'environment.json').write_text(json.dumps({'LEAN_PATH': env['LEAN_PATH']}, indent=2))
            old_modules = {m['module']: m for m in previous.get('modules', [])}
            failed = set()
            for module in ordered:
                blocked = [d for d in dependencies[module] if d in failed]
                if blocked:
                    failed.add(module)
                    report['modules'].append({'module': module, 'returncode': None,
                                              'blocked_by': blocked})
                    print('BLOCKED', module, blocked, flush=True)
                    continue
                rel = Path(module.replace('.', '/'))
                output = (lib / rel).with_suffix('.olean')
                output.parent.mkdir(parents=True, exist_ok=True)
                old = old_modules.get(module, {})
                files = old.get('artifacts', {})
                reuse = (args.incremental and previous.get('lean_version') == version
                         and previous.get('fingerprints', {}).get(module) == fingerprints[module]
                         and old.get('returncode') == 0 and files
                         and (not owned(module) or old.get('warnings') == 0)
                         and all((out / p).is_file() and digest(out / p) == h for p, h in files.items()))
                if reuse:
                    report['modules'].append({**old, 'reused': True})
                    print('REUSE', module, flush=True)
                    continue
                result = subprocess.run([lean, '-o', str(output), str((source / rel).with_suffix('.lean'))],
                    cwd=source, env=env, pass_fds=pass_fds, text=True,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                (out / (module + '.log')).write_text(result.stdout)
                warnings = len(re.findall(r'\bwarning:', result.stdout))
                files = {str(p.relative_to(out)): digest(p)
                         for p in output.parent.glob(output.stem + '.olean*')} if result.returncode == 0 else {}
                report['modules'].append({'module': module, 'returncode': result.returncode,
                                          'warnings': warnings, 'artifacts': files, 'reused': False})
                print('CHECK', module, 'exit', result.returncode, 'warnings', warnings, flush=True)
                if result.returncode or (warnings and owned(module)):
                    print(result.stdout, flush=True)
                    failed.add(module)
            if failed:
                raise RuntimeError('Compilation or new-module warnings failed: ' + ', '.join(sorted(failed)))
            if not args.skip_audit:
                audit = source / 'PeirceSuperoperatorsAudit.lean'
                header = ('/-\nCopyright (c) 2026 InfoGeometry Authors. All rights reserved.\n'
                          'Released under Apache 2.0 license as described in the file LICENSE.\n'
                          'Authors: InfoGeometry Engine Contributors\n-/\n')
                audit.write_text(header + audit_source(targets))
                result = subprocess.run([lean, str(audit)], cwd=source, env=env,
                    pass_fds=pass_fds, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                (out / 'axioms.log').write_text(result.stdout)
                if result.returncode or re.search(r'\bwarning:', result.stdout):
                    raise RuntimeError('Native axiom audit failed; see axioms.log')
                report['declaration_counts'] = parse_audit_output(result.stdout, targets)
                report['axioms'] = re.findall(r'^AUDIT_AXIOMS: (.*)$', result.stdout, re.MULTILINE)
                print('AXIOM AUDIT', report['declaration_counts'], report['axioms'], flush=True)
            for module, expected in hashes.items():
                if digest(ROOT / 'lean' / (module.replace('.', '/') + '.lean')) != expected:
                    raise RuntimeError('Source changed during verification: ' + module)
                if digest(source / (module.replace('.', '/') + '.lean')) != expected:
                    raise RuntimeError('Copied source changed during verification: ' + module)
            for path, expected in helper_hashes.items():
                if digest(ROOT / path) != expected:
                    raise RuntimeError('Verification implementation changed: ' + path)
            if run(['git', 'rev-parse', 'HEAD'], mathlib, pass_fds=pass_fds) != pin:
                raise RuntimeError('Mathlib revision changed during verification')
            run(['git', 'diff', '--exit-code', 'HEAD', '--'], mathlib, pass_fds=pass_fds)
            report['status'] = 'development_passed' if args.skip_audit else 'passed'
            print(report['status'].upper(), flush=True)
    except Exception as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        report_path.write_text(json.dumps(report, indent=2) + '\n')
        evidence = [report_path, *sorted(out.glob('*.log'))]
        if (out / 'environment.json').exists():
            evidence.append(out / 'environment.json')
        generated_audit = out / 'src/PeirceSuperoperatorsAudit.lean'
        if generated_audit.exists():
            evidence.append(generated_audit)
        manifest = {str(p.relative_to(out)): digest(p) for p in evidence}
        manifest.update({'repository/' + p: digest(ROOT / p) for p in helpers})
        (out / 'evidence-sha256.json').write_text(json.dumps(manifest, indent=2) + '\n')


if __name__ == '__main__':
    main()
