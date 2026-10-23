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
import sys

if __package__ in (None, ""):
    from reviewed_audit_source import (audit_source, validate_targets, validate_roles,
                                       check_command_sources, may_reuse_cache, parse_audit_output)
else:
    from .reviewed_audit_source import (audit_source, validate_targets, validate_roles,
                                        check_command_sources, may_reuse_cache, parse_audit_output)


def run(cmd, cwd, env=None, pass_fds=()):
    result = subprocess.run(cmd, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, pass_fds=pass_fds)
    if result.returncode:
        raise RuntimeError(f"{cmd!r}\n{result.stdout}")
    return result.stdout


def run_logged(cmd, cwd, log, env=None, pass_fds=()):
    result = subprocess.run(cmd, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, pass_fds=pass_fds)
    log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"{cmd!r} exited {result.returncode}; see {log}")
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



def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mode', choices=('copied', 'native'), default='copied')
    parser.add_argument('--mathlib-root', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cache-dir', type=Path)
    parser.add_argument('--wait-for-build-lock', action='store_true')
    parser.add_argument('--clean-release', action='store_true')
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    if args.mode == 'native':
        if args.mathlib_root is not None or args.cache_dir is not None:
            parser.error('native mode uses repository dependencies and caches')
        sys.path.insert(0, str(repo))
        from tools.quality.reviewed_native import run_native
        run_native(repo, args.output, wait=args.wait_for_build_lock,
                   clean_release=args.clean_release)
        return
    if args.mathlib_root is None:
        parser.error('--mathlib-root is required in copied mode')
    if args.clean_release or args.wait_for_build_lock:
        parser.error('--clean-release and --wait-for-build-lock require native mode')
    mathlib, output = args.mathlib_root.resolve(), args.output.resolve()
    cache = args.cache_dir.resolve() if args.cache_dir else None
    specification = json.loads((repo / 'tools/quality/reviewed_prs_20260921.json').read_text())
    targets = validate_targets(specification['targets'])
    command_only = validate_roles(targets)
    output.mkdir(parents=True, exist_ok=False)
    report = {'status': 'pending', 'modules': [], 'targets': targets,
              'revision': run(['git', 'rev-parse', 'HEAD'], repo).strip(),
              'scope': 'Reviewed source modules, complete repository import closure, combined import and axiom audit; excludes exhaustive aggregators'}
    try:
        check_command_sources(repo / 'lean', targets, command_only)
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
            pass_fds = (lock.fileno(),)
            active = run(['ps', '-eo', 'comm='], repo, pass_fds=pass_fds).splitlines()
            if any(n.strip() in {'lean', 'lake', 'leanc'} for n in active):
                raise RuntimeError('Another Lean/Lake build is active')
            print(f'Fetching pinned cache for {len(native)} Mathlib roots', flush=True)
            print(run(['lake', 'exe', 'cache', 'get', *sorted(native)], mathlib, pass_fds=pass_fds), flush=True)
            env = os.environ.copy()
            base_path = run(['lake', 'env', 'printenv', 'LEAN_PATH'], mathlib, pass_fds=pass_fds).strip()
            paths = [str((mathlib / p).resolve()) if not Path(p).is_absolute() else p
                     for p in base_path.split(os.pathsep) if p]
            env['LEAN_PATH'] = os.pathsep.join([str(lib), *paths])
            print(run(['lean', '--version'], source, env, pass_fds=pass_fds), flush=True)
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
                if metadata and metadata.is_file() and may_reuse_cache(module, targets, command_only):
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
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, pass_fds=pass_fds)
                (output / (module + '.log')).write_text(result.stdout)
                report['modules'].append({'module': module,
                    'status': 'failed' if result.returncode else 'passed',
                    'warnings': result.stdout.count('warning:'),
                    'cached': False, 'exit_code': result.returncode,
                    'log': str(output / (module + '.log')),
                    'role': 'command_only' if module in command_only else 'owner'})
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
            check_command_sources(source, targets, command_only)
            audit.write_text(audit_source(targets, command_only))
            axioms = run_logged(['lean', str(audit)], source, output / 'axioms.log', env, pass_fds=pass_fds)
            counts = parse_audit_output(axioms, targets, command_only)
            for module in command_only:
                records = [entry for entry in report['modules'] if entry['module'] == module]
                if len(records) != 1 or records[0].get('cached') is not False or records[0].get('exit_code') != 0:
                    raise RuntimeError(f'Missing fresh command execution: {module}')
            # The existing explicit proof probe is also checked from its exact source.
            probe = source / 'PolarizedShearSpinAudit.lean'
            shutil.copy2(repo / 'proofs/PolarizedShearSpinAudit.lean', probe)
            run_logged(['lean', str(probe)], source, output / 'polarized-probe.log', env, pass_fds=pass_fds)
            check_command_sources(repo / 'lean', targets, command_only)
            check_command_sources(source, targets, command_only)
            report.update(status='passed', audited_declarations=sum(counts.values()), module_counts=counts,
                          command_only_modules=list(command_only))
            print(f'Passed {len(ordered)} modules; audited {sum(counts.values())} declarations', flush=True)
    except Exception as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
