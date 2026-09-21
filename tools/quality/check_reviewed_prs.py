#!/usr/bin/env python3
"""Kernel-check the reviewed PR union with the repository's exact dependency pins."""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


def run(cmd, cwd, env=None):
    result = subprocess.run(cmd, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"{cmd!r}\n{result.stdout}")
    return result.stdout


def closure(repo, targets):
    ordered, dependencies, native, active = [], {}, set(), set()

    def visit(module):
        if module in active:
            raise RuntimeError(f"Import cycle at {module}")
        if module in dependencies:
            return
        active.add(module)
        path = repo / 'lean' / (module.replace('.', '/') + '.lean')
        deps = []
        for line in path.read_text().splitlines():
            if not line.startswith('import '):
                continue
            for dep in line[7:].split('--', 1)[0].split():
                source = repo / 'lean' / (dep.replace('.', '/') + '.lean')
                if source.is_file():
                    visit(dep)
                    deps.append(dep)
                elif dep == 'Mathlib' or dep.startswith('Mathlib.'):
                    native.add(dep.replace('.', '/') + '.lean')
                elif dep.split('.')[0] not in {'Lean', 'Std', 'Init'}:
                    raise RuntimeError(f"Unresolved repository import: {module} -> {dep}")
        active.remove(module)
        dependencies[module] = deps
        ordered.append(module)

    for target in targets:
        visit(target)
    return ordered, dependencies, native


def audit_source(targets):
    imports = '\n'.join('import ' + m for m in targets)
    module_names = ', '.join('`' + m for m in targets)
    return imports + '\nimport Lean.Util.CollectAxioms\nimport Lean.Elab.Command\n\nopen Lean Elab Command\n\n' + f'''run_cmd do
  let env ← getEnv
  let targets : Array Name := #[{module_names}]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, info) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    if !targets.contains owner then continue
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial declaration in reviewed module: {{name}}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {{ax}} in {{name}}"
    count := count + 1
    logInfo m!"AUDIT_DECL: {{owner}}: {{name}}: {{axioms}}"
  if count == 0 then throwError "No declarations audited"
  logInfo m!"AUDIT_COUNT: {{count}}"
'''


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mathlib-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cache-dir', type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    mathlib, output = args.mathlib_root.resolve(), args.output.resolve()
    cache = args.cache_dir.resolve() if args.cache_dir else None
    output.mkdir(parents=True, exist_ok=True)
    specification = json.loads((repo / 'tools/quality/reviewed_prs_20260921.json').read_text())
    targets = specification['targets']
    report = {'status': 'pending', 'modules': [], 'targets': targets,
              'revision': run(['git', 'rev-parse', 'HEAD'], repo).strip(),
              'scope': 'Reviewed source modules, complete repository import closure, combined import and axiom audit; excludes exhaustive aggregators'}
    try:
        manifest = json.loads((repo / 'lake-manifest.json').read_text())
        pinned = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
        toolchain = (repo / 'lean-toolchain').read_text()
        if run(['git', 'rev-parse', 'HEAD'], mathlib).strip() != pinned:
            raise RuntimeError('Mathlib revision differs from repository pin')
        if (mathlib / 'lean-toolchain').read_text() != toolchain:
            raise RuntimeError('Mathlib and repository Lean versions differ')
        report.update(mathlib=pinned, toolchain=toolchain.strip())
        ordered, dependencies, native = closure(repo, targets)
        fingerprints, source_hashes = {}, {}
        for module in ordered:
            path = repo / 'lean' / (module.replace('.', '/') + '.lean')
            source_hashes[module] = hashlib.sha256(path.read_bytes()).hexdigest()
            payload = [1, module, toolchain, pinned, source_hashes[module],
                       [fingerprints[d] for d in dependencies[module]]]
            fingerprints[module] = hashlib.sha256(json.dumps(payload).encode()).hexdigest()
        report['source_sha256'] = source_hashes
        source, lib = output / 'src', output / 'lib'
        source.mkdir(exist_ok=True)
        lib.mkdir(exist_ok=True)
        (source / 'lean-toolchain').write_text(toolchain)
        for module in ordered:
            rel = Path(module.replace('.', '/') + '.lean')
            (source / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(repo / 'lean' / rel, source / rel)
        with open('/tmp/info-geometry-build.lock', 'a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            active = run(['ps', '-eo', 'comm='], repo).splitlines()
            if any(n.strip() in {'lean', 'lake', 'leanc'} for n in active):
                raise RuntimeError('Another Lean/Lake build is active')
            print(f'Fetching pinned cache for {len(native)} Mathlib roots', flush=True)
            print(run(['lake', 'exe', 'cache', 'get', *sorted(native)], mathlib), flush=True)
            env = os.environ.copy()
            base_path = run(['lake', 'env', 'printenv', 'LEAN_PATH'], mathlib).strip()
            paths = [str((mathlib / p).resolve()) if not Path(p).is_absolute() else p
                     for p in base_path.split(os.pathsep) if p]
            env['LEAN_PATH'] = os.pathsep.join([str(lib), *paths])
            print(run(['lean', '--version'], source, env), flush=True)
            failed = set()
            for module in ordered:
                blocked = [d for d in dependencies[module] if d in failed]
                if blocked:
                    failed.add(module)
                    report['modules'].append({'module': module, 'status': 'blocked', 'dependencies': blocked})
                    print(f'Blocked {module}: {blocked}', flush=True)
                    continue
                rel = Path(module.replace('.', '/'))
                destination = (lib / rel).with_suffix('.olean')
                destination.parent.mkdir(parents=True, exist_ok=True)
                cached = cache / fingerprints[module] if cache else None
                metadata = cached / 'metadata.json' if cached else None
                if metadata and metadata.is_file():
                    record = json.loads(metadata.read_text())
                    files = record.get('files', {})
                    valid = (record.get('module') == module and
                             destination.name in files and all(
                                 Path(name).name == name and (cached / name).is_file() and
                                 hashlib.sha256((cached / name).read_bytes()).hexdigest() == digest
                                 for name, digest in files.items()))
                    if valid:
                        for name in files:
                            shutil.copy2(cached / name, destination.parent / name)
                        report['modules'].append({'module': module, 'status': 'passed',
                            'cached': True, 'warnings': record['warnings']})
                        print(f'Reusing exact-source kernel output: {module}', flush=True)
                        continue
                print(f'Checking {module}', flush=True)
                result = subprocess.run(['lean', '-o', str(destination),
                                         str((source / rel).with_suffix('.lean'))],
                                        cwd=source, env=env, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                (output / (module + '.log')).write_text(result.stdout)
                report['modules'].append({'module': module,
                    'status': 'failed' if result.returncode else 'passed',
                    'warnings': result.stdout.count('warning:')})
                if result.returncode:
                    failed.add(module)
                elif cached:
                    cached.mkdir(parents=True, exist_ok=True)
                    files = {}
                    for built in destination.parent.glob(destination.stem + '.*'):
                        if built.is_file() and built.name.endswith(
                                ('.olean', '.olean.private', '.olean.server', '.ilean')):
                            shutil.copy2(built, cached / built.name)
                            files[built.name] = hashlib.sha256(built.read_bytes()).hexdigest()
                    metadata.write_text(json.dumps({'module': module, 'files': files,
                        'warnings': result.stdout.count('warning:')}))
                if result.stdout:
                    print(result.stdout, flush=True)
            if failed:
                raise RuntimeError('Compilation failed or blocked: ' + ', '.join(sorted(failed)))
            # Import the entire union, then enumerate the actual compiled environment.
            # This includes private/generated declarations and instances; no source regex.
            audit = source / 'ReviewedPRsAudit.lean'
            audit.write_text(audit_source(targets))
            axioms = run(['lean', str(audit)], source, env)
            (output / 'axioms.log').write_text(axioms)
            count = re.findall(r'AUDIT_COUNT: (\d+)', axioms)
            if len(count) != 1 or int(count[0]) <= 0:
                raise RuntimeError('Missing completed native declaration audit')
            # The existing explicit proof probe is also checked from its exact source.
            probe = source / 'PolarizedShearSpinAudit.lean'
            shutil.copy2(repo / 'proofs/PolarizedShearSpinAudit.lean', probe)
            (output / 'polarized-probe.log').write_text(run(['lean', str(probe)], source, env))
            report.update(status='passed', audited_declarations=int(count[0]))
            print(f'Passed {len(ordered)} modules; audited {count[0]} declarations', flush=True)
    except Exception as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
