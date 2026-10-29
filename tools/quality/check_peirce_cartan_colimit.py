#!/usr/bin/env python3
"""Exact-pin, sequential source-closure check for Peirce/Cartan/colimit sources.

Reuses the repository's closure resolver and native axiom-audit generator.
Independent branches continue after an error; dependent modules are blocked.
No dependency revisions, source imports, or caches are rewritten or removed.
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
from tools.quality.check_peirce_reflection import audit_source

TARGETS = [
    'InfoGeometry.Core.DualSeedCartan',
    'InfoGeometry.OperatorAlgebra.PeirceCoupling.StarReflection',
    'InfoGeometry.OperatorAlgebra.PeirceCoupling.RealReflectionGeometry',
    'InfoGeometry.OperatorAlgebra.PeirceCoupling.CartanDirectLimit',
    'InfoGeometry.OperatorAlgebra.PeirceCoupling.RealCartanWitnesses',
    'InfoGeometry.OperatorAlgebra.PeirceCoupling.StarDirectLimit',
    'InfoGeometry.OperatorAlgebra.PeirceCartanColimit',
    'InfoGeometry.OperatorAlgebra.PeirceCoupling',
]


def run(cmd, cwd, env=None):
    result = subprocess.run(cmd, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'{cmd!r}\n{result.stdout}')
    return result.stdout


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mathlib-root', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    mathlib, out = args.mathlib_root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    state = {'status': 'pending', 'scope': 'exact source closure; not root Lake build',
             'targets': TARGETS, 'modules': [], 'axiom_audit_passed': False}
    try:
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
        pin = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
        toolchain = (ROOT / 'lean-toolchain').read_text().strip()
        state.update(revision=run(['git', 'rev-parse', 'HEAD'], ROOT).strip(),
                     mathlib=pin, toolchain=toolchain)
        if run(['git', 'rev-parse', 'HEAD'], mathlib).strip() != pin:
            raise RuntimeError('Mathlib revision mismatch')
        if (mathlib / 'lean-toolchain').read_text().strip() != toolchain:
            raise RuntimeError('Toolchain mismatch')
        ordered, dependencies, native = closure(ROOT, TARGETS)
        state['module_import_dag'] = dependencies
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
            (out / 'cache.log').write_text(run(['lake', 'exe', 'cache', 'get', *sorted(native)], mathlib))
            env = os.environ.copy()
            path = run(['lake', 'env', 'printenv', 'LEAN_PATH'], mathlib).strip()
            search = [str((mathlib / p).resolve()) if not Path(p).is_absolute() else p
                      for p in path.split(os.pathsep) if p]
            env['LEAN_PATH'] = os.pathsep.join([str(lib), *search])
            (out / 'lean-version.txt').write_text(run(['lean', '--version'], src, env))
            failed = set()
            for module in ordered:
                blocked = [d for d in dependencies[module] if d in failed]
                if blocked:
                    failed.add(module)
                    state['modules'].append({'module': module, 'status': 'blocked',
                                             'dependencies': blocked})
                    print('BLOCKED', module, blocked, flush=True)
                    continue
                rel = Path(module.replace('.', '/'))
                olean = (lib / rel).with_suffix('.olean')
                olean.parent.mkdir(parents=True, exist_ok=True)
                command = ['lean']
                if module in TARGETS:
                    command.append('-DwarningAsError=true')
                command += ['-o', str(olean), str((src / rel).with_suffix('.lean'))]
                result = subprocess.run(command, cwd=src, env=env, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                (out / (module + '.log')).write_text(result.stdout)
                state['modules'].append({'module': module, 'returncode': result.returncode,
                                         'warnings': result.stdout.count('warning:'),
                                         'status': 'failed' if result.returncode else 'passed'})
                print('CHECK', module, result.returncode, flush=True)
                print(result.stdout, flush=True)
                if result.returncode:
                    failed.add(module)
            if failed:
                raise RuntimeError('Failed or blocked modules: ' + ', '.join(sorted(failed)))
            audit = src / 'PeirceCartanColimitKernelAudit.lean'
            audit.write_text(audit_source(TARGETS))
            evidence = run(['lean', str(audit)], src, env)
            (out / 'audit.log').write_text(evidence)
            if 'AUDIT_COUNT:' not in evidence:
                raise RuntimeError('Native declaration audit did not finish')
            state.update(status='passed', axiom_audit_passed=True)
            print(evidence, flush=True)
    except Exception as error:
        state.update(status='failed', error=str(error))
        raise
    finally:
        (out / 'status.json').write_text(json.dumps(state, indent=2) + '\n')


if __name__ == '__main__':
    main()
