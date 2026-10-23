#!/usr/bin/env python3
"""Compile exact causal-attention sources against the repository-pinned Mathlib.

This is a scoped source-closure check, not a root-package build. Existing import
resolution is reused; auditing uses Lean 4.34.1 public collectAxioms and the
same native declaration enumeration and foundational-axiom allowlist.
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

TARGETS = [
    'InfoGeometry.Routing.CausalPrefixPooling',
    'InfoGeometry.Routing.FiniteLogSinkhorn',
    'InfoGeometry.Routing.PrefixCausalDifferential',
    'InfoGeometry.Routing.BlockCausalSinkhorn',
]


def audit_source(targets):
    """Use the public pinned-Lean collector, never its private implementation."""
    imports = '\n'.join('import ' + module for module in targets)
    names = ', '.join('`' + module for module in targets)
    return imports + '''
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let targets : Array Name := #[TARGET_NAMES]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut allAxioms : Array Name := #[]
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    if !targets.contains owner then continue
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial declaration in reviewed module: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {ax} in {name}"
      unless allAxioms.contains ax do
        allAxioms := allAxioms.push ax
    count := count + 1
    logInfo m!"AUDIT_DECL: {owner}: {name}: {axioms}"
  if count == 0 then throwError "No declarations audited"
  logInfo m!"AUDIT_AXIOMS: {allAxioms}"
  logInfo m!"AUDIT_COUNT: {count}"
'''.replace('TARGET_NAMES', names)


def run(args, cwd, env=None):
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'{args!r}\n{result.stdout}')
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
        ordered, _, _ = closure(ROOT, TARGETS)
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
            path = run(['lake', 'env', 'printenv', 'LEAN_PATH'], mathlib).strip()
            search = [str((mathlib / p).resolve()) if not Path(p).is_absolute() else p
                      for p in path.split(os.pathsep) if p]
            env['LEAN_PATH'] = os.pathsep.join([str(lib), *search])
            (out / 'lean-version.txt').write_text(run(['lean', '--version'], src, env))
            for module in ordered:
                rel = Path(module.replace('.', '/'))
                olean = (lib / rel).with_suffix('.olean')
                olean.parent.mkdir(parents=True, exist_ok=True)
                result = subprocess.run(['lean', '-o', str(olean),
                    str((src / rel).with_suffix('.lean'))], cwd=src, env=env,
                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                (out / (module + '.log')).write_text(result.stdout)
                state['modules'].append({'module': module, 'returncode': result.returncode})
                print('CHECK', module, result.returncode, flush=True)
                print(result.stdout, flush=True)
                if result.returncode:
                    raise RuntimeError('Compilation failed: ' + module)
            audit = src / 'BlockCausalAudit.lean'
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
