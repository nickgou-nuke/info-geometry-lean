#!/usr/bin/env python3
"""Check exact source closure and native transitive axioms; no dependency changes."""
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


def run(cmd, cwd, env=None):
    p = subprocess.run(cmd, cwd=cwd, env=env, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if p.returncode:
        raise RuntimeError(f"{cmd!r}\n{p.stdout}")
    return p.stdout


def main():
    ap = argparse.ArgumentParser(__doc__)
    ap.add_argument('--mathlib-root', required=True, type=Path)
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    out, mathlib = args.output.resolve(), args.mathlib_root.resolve()
    out.mkdir(parents=True, exist_ok=True)
    targets = json.loads((ROOT / 'tools/quality/perjes_targets.json').read_text())
    state = {'status': 'pending', 'scope': 'exact transitive source closure, not root package',
             'targets': targets, 'modules': [], 'axiom_audit_passed': False}
    try:
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
        pin = next(x['rev'] for x in manifest['packages'] if x['name'] == 'mathlib')
        toolchain = (ROOT / 'lean-toolchain').read_text().strip()
        state.update(revision=run(['git', 'rev-parse', 'HEAD'], ROOT).strip(),
                     mathlib=pin, toolchain=toolchain)
        assert run(['git', 'rev-parse', 'HEAD'], mathlib).strip() == pin, 'Mathlib pin mismatch'
        assert (mathlib / 'lean-toolchain').read_text().strip() == toolchain, 'Toolchain mismatch'
        ordered, deps, native = closure(ROOT, targets)
        src, lib = out / 'src', out / 'lib'
        src.mkdir(exist_ok=True)
        lib.mkdir(exist_ok=True)
        (src / 'lean-toolchain').write_text(toolchain + '\n')
        hashes = {}
        for module in ordered:
            rel = Path(module.replace('.', '/') + '.lean')
            data = (ROOT / 'lean' / rel).read_bytes()
            dst = src / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(data)
            hashes[module] = hashlib.sha256(data).hexdigest()
        state['source_sha256'] = hashes
        with open('/tmp/info-geometry-build.lock', 'a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            active = run(['ps', '-eo', 'comm='], ROOT).splitlines()
            if any(x.strip() in {'lean', 'lake', 'leanc'} for x in active):
                raise RuntimeError('Another compiler is active')
            (out / 'cache.log').write_text(run(['lake', 'exe', 'cache', 'get', *sorted(native)], mathlib))
            paths = run(['lake', 'env', 'printenv', 'LEAN_PATH'], mathlib).strip().split(os.pathsep)
            paths = [str((mathlib / p).resolve()) if not Path(p).is_absolute() else p for p in paths if p]
            env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(lib), *paths]))
            (out / 'lean-version.txt').write_text(run(['lean', '--version'], src, env))
            failed = set()
            for module in ordered:
                if any(d in failed for d in deps[module]):
                    failed.add(module)
                    state['modules'].append({'module': module, 'status': 'blocked'})
                    continue
                rel = Path(module.replace('.', '/'))
                olean = (lib / rel).with_suffix('.olean')
                olean.parent.mkdir(parents=True, exist_ok=True)
                p = subprocess.run(['lean', '-o', str(olean), str((src / rel).with_suffix('.lean'))],
                                   cwd=src, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                (out / (module + '.log')).write_text(p.stdout)
                print('CHECK', module, p.returncode, flush=True)
                print(p.stdout, flush=True)
                state['modules'].append({'module': module, 'status': 'failed' if p.returncode else 'passed',
                                         'returncode': p.returncode, 'warnings': p.stdout.count('warning:')})
                if p.returncode:
                    failed.add(module)
            if failed:
                raise RuntimeError('Failed or blocked source modules: ' + ', '.join(sorted(failed)))
            audit = src / 'PerjesKernelAudit.lean'
            audit.write_text(audit_source(targets))
            evidence = run(['lean', str(audit)], src, env)
            (out / 'audit.log').write_text(evidence)
            if 'AUDIT_COUNT:' not in evidence:
                raise RuntimeError('Empty audit')
            state.update(status='passed', axiom_audit_passed=True)
            print(evidence, flush=True)
    except Exception as exc:
        state.update(status='failed', error=str(exc))
        raise
    finally:
        (out / 'status.json').write_text(json.dumps(state, indent=2) + '\n')


if __name__ == '__main__':
    main()
