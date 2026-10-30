#!/usr/bin/env python3
"""Check exact Wheeler sources against unchanged pins; never certify the root build."""
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

TARGETS = ['InfoGeometry.WheelerEpilogue',
           'InfoGeometry.WheelerEpilogueWitness',
           'InfoGeometry.WheelerEpilogueRegression']


def main() -> None:
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mathlib-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    mathlib, out = args.mathlib_root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    state = {'status': 'pending', 'scope': 'exact source closure, not root Lake build',
             'targets': TARGETS, 'modules': [], 'source_sha256': {}}

    def run(command: list[str], cwd: Path, log: str, env=None) -> str:
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / log).write_text(result.stdout, encoding='utf-8')
        print(result.stdout, end='', flush=True)
        if result.returncode:
            raise RuntimeError(f'{command!r} exited {result.returncode}; see {log}')
        return result.stdout

    try:
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
        pin = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
        toolchain = (ROOT / 'lean-toolchain').read_text().strip()
        state['revision'] = run(['git', 'rev-parse', 'HEAD'], ROOT, 'revision.log').strip()
        state.update(mathlib=pin, toolchain=toolchain)
        if run(['git', 'rev-parse', 'HEAD'], mathlib, 'mathlib.log').strip() != pin:
            raise RuntimeError('Mathlib revision mismatch')
        if (mathlib / 'lean-toolchain').read_text().strip() != toolchain:
            raise RuntimeError('Toolchain mismatch')
        ordered, _, _ = closure(ROOT, TARGETS)
        src, lib = out / 'src', out / 'lib'
        src.mkdir(exist_ok=True)
        lib.mkdir(exist_ok=True)
        (src / 'lean-toolchain').write_text(toolchain + '\n')
        for module in ordered:
            rel = Path(module.replace('.', '/') + '.lean')
            data = (ROOT / 'lean' / rel).read_bytes()
            dest = src / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
            state['source_sha256'][module] = hashlib.sha256(data).hexdigest()
        audit = ROOT / 'tests/WheelerEpilogueAudit.lean'
        (src / audit.name).write_bytes(audit.read_bytes())
        state['audit_source_sha256'] = hashlib.sha256(audit.read_bytes()).hexdigest()
        with open('/tmp/info-geometry-build.lock', 'a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            processes = run(['ps', '-eo', 'comm='], ROOT, 'processes.log').splitlines()
            if any(p.strip() in {'lean', 'lake', 'leanc'} for p in processes):
                raise RuntimeError('Concurrent compiler detected')
            run(['lake', 'exe', 'cache', 'get'], mathlib, 'cache.log')
            path = run(['lake', 'env', 'printenv', 'LEAN_PATH'], mathlib, 'lean-path.log').strip()
            search = [str((mathlib / p).resolve()) if not Path(p).is_absolute() else p
                      for p in path.split(os.pathsep) if p]
            env = os.environ.copy()
            env['LEAN_PATH'] = os.pathsep.join([str(lib), *search])
            state['lean_version'] = run(['lean', '--version'], src, 'lean-version.log', env).strip()
            for module in ordered:
                rel = Path(module.replace('.', '/'))
                olean = (lib / rel).with_suffix('.olean')
                olean.parent.mkdir(parents=True, exist_ok=True)
                cmd = ['lean']
                if module in TARGETS:
                    cmd.append('-DwarningAsError=true')
                cmd += ['-o', str(olean), str((src / rel).with_suffix('.lean'))]
                print('CHECK', module, flush=True)
                run(cmd, src, module + '.log', env)
                state['modules'].append({'module': module, 'returncode': 0})
            evidence = run(['lean', str(src / audit.name)], src, 'audit.log', env)
            records = [json.loads(line) for line in evidence.splitlines()
                       if line.startswith('{')]
            summaries = [r for r in records if r.get('record') == 'summary']
            if not summaries or summaries[-1].get('status') != 'PASS':
                raise RuntimeError('Native audit did not finish')
            decls = [r for r in records if r.get('record') == 'declaration']
            if not decls:
                raise RuntimeError('Empty mathematical declaration audit')
            names = {r['name'] for r in decls}
            edges = {(d, r['name']) for r in decls
                     for d in r['dependencies'] if d in names}
            remaining, done, layers = set(names), set(), []
            while remaining:
                layer = sorted(n for n in remaining
                               if all(a in done for a, b in edges if b == n))
                if not layer:
                    raise RuntimeError('Cyclic declaration graph')
                layers.append(layer)
                done.update(layer)
                remaining.difference_update(layer)
            graph = {'orientation': 'dependency -> dependent',
                     'source': 'native type/value constant references',
                     'nodes': sorted(names), 'direct_edges': sorted(edges), 'layers': layers}
            (out / 'dependency-order.json').write_text(json.dumps(graph, indent=2) + '\n')
            state.update(status='passed', axiom_audit_passed=True,
                         audited_declarations=len(decls),
                         meta_tooling=[r for r in records if r.get('record') == 'meta_tooling'])
    except Exception as error:
        state.update(status='failed', error=str(error))
        raise
    finally:
        (out / 'status.json').write_text(json.dumps(state, indent=2) + '\n')


if __name__ == '__main__':
    main()
