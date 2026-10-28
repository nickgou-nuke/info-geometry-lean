#!/usr/bin/env python3
"""Check the exact Lie–Jordan/Peirce source closure at repository dependency pins.

This is a scoped check, not a build of the repository's exhaustive aggregators.
It compiles exact source copies, audits every declaration in the repository
import closure, and builds that closure in an isolated native Lake package.
Existing repository and dependency manifests are never edited.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.build_lock import BuildLock, DEFAULT_BUILD_LOCK_PATH
from tools.quality.audit_constructivity import scan_file
from tools.quality.check_reviewed_prs import closure
from tools.quality.reviewed_audit_source import audit_source, parse_audit_output

TARGETS = [
    'InfoGeometry.Core.LieJordanComposition',
    'InfoGeometry.Core.OperatorCliffordDouble',
    'InfoGeometry.Core.PeirceStarCharges',
    'InfoGeometry.Canonical.LieJordanMatrixGeometry',
    'InfoGeometry.Canonical.LieJordanMatrixExamples',
]


def run(command, cwd, env=None, log=None, pass_fds=()):
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            pass_fds=pass_fds)
    if log is not None:
        log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f'{command!r} exited {result.returncode}\n{result.stdout}')
    return result.stdout


def assert_clean_dependency(path):
    if run(['git', 'status', '--porcelain', '--untracked-files=normal'], path).strip():
        raise RuntimeError('Dependency source differs from its pinned checkout: ' + str(path))


def make_lake_package(directory, source, mathlib, toolchain):
    """Use real path dependencies; do not symlink or mutate any existing cache."""
    directory.mkdir(exist_ok=True)
    (directory / 'lean-toolchain').write_text(toolchain)
    roots = ', '.join('`' + module for module in TARGETS)
    (directory / 'lakefile.lean').write_text(
        'import Lake\nopen Lake DSL\npackage lieJordanVerification\n'
        f'require mathlib from {json.dumps(str(mathlib))}\n'
        '@[default_target] lean_lib InfoGeometry where\n'
        f'  srcDir := {json.dumps(str(source))}\n  roots := #[{roots}]\n')
    native = json.loads((mathlib / 'lake-manifest.json').read_text())
    packages = []
    for package in native['packages']:
        dependency = mathlib / native['packagesDir'] / package['name']
        if run(['git', 'rev-parse', 'HEAD'], dependency).strip() != package['rev']:
            raise RuntimeError('Transitive dependency pin mismatch: ' + package['name'])
        assert_clean_dependency(dependency)
        packages.append({
            'type': 'path', 'name': package['name'], 'scope': package.get('scope', ''),
            'dir': str(dependency), 'inherited': True,
            'manifestFile': package['manifestFile'], 'configFile': package['configFile'],
        })
    packages.insert(0, {
        'type': 'path', 'name': 'mathlib', 'scope': '', 'dir': str(mathlib),
        'inherited': False, 'manifestFile': 'lake-manifest.json', 'configFile': 'lakefile.lean',
    })
    (directory / 'lake-manifest.json').write_text(json.dumps({
        'version': native['version'], 'packagesDir': '.lake/packages', 'packages': packages,
        'name': 'lieJordanVerification', 'lakeDir': '.lake', 'fixedToolchain': True,
    }, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mathlib-root', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    mathlib, out = args.mathlib_root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    state = {'status': 'pending', 'targets': TARGETS, 'modules': [],
             'scope': 'exact source closure and isolated native Lake package; not root package'}
    try:
        manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
        pin = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
        toolchain = (ROOT / 'lean-toolchain').read_text()
        if run(['git', 'rev-parse', 'HEAD'], mathlib).strip() != pin:
            raise RuntimeError('Mathlib revision mismatch')
        if (mathlib / 'lean-toolchain').read_text() != toolchain:
            raise RuntimeError('Toolchain mismatch')
        assert_clean_dependency(mathlib)
        state.update(revision=run(['git', 'rev-parse', 'HEAD'], ROOT).strip(),
                     mathlib=pin, toolchain=toolchain.strip(),
                     working_tree_status=run(['git', 'status', '--porcelain'], ROOT))
        ordered, dependencies, native = closure(ROOT, TARGETS)
        state['dependencies'] = dependencies
        state['source_sha256'] = {}
        state['constructivity_findings'] = []
        src, lib = out / 'src', out / 'lib'
        src.mkdir(exist_ok=True)
        lib.mkdir(exist_ok=True)
        (src / 'lean-toolchain').write_text(toolchain)
        for module in ordered:
            rel = Path(module.replace('.', '/') + '.lean')
            path = ROOT / 'lean' / rel
            raw = path.read_bytes()
            state['constructivity_findings'].extend(asdict(f) for f in scan_file(path))
            destination = src / rel
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(raw)
            state['source_sha256'][module] = hashlib.sha256(raw).hexdigest()
        if state['constructivity_findings']:
            raise RuntimeError('Exact source constructivity scan failed')
        with BuildLock(DEFAULT_BUILD_LOCK_PATH, f'lie-jordan-check:{os.getpid()}', block=True) as lock:
            fds = (lock.fileno(),)
            processes = run(['ps', '-eo', 'stat=,comm='], ROOT).splitlines()
            if any(p.split()[-1] in {'lean', 'lake', 'leanc'} and
                   not p.split()[0].startswith('Z') for p in processes):
                raise RuntimeError('Concurrent compiler detected')
            run(['lake', 'exe', 'cache', 'get', *sorted(native)], mathlib,
                log=out / 'cache.log', pass_fds=fds)
            env = os.environ.copy()
            path = run(['lake', 'env', 'printenv', 'LEAN_PATH'], mathlib,
                       pass_fds=fds).strip()
            search = [str((mathlib / p).resolve()) if not Path(p).is_absolute() else p
                      for p in path.split(os.pathsep) if p]
            env['LEAN_PATH'] = os.pathsep.join([str(lib), *search])
            state['lean_version'] = run(['lean', '--version'], src, env, pass_fds=fds).strip()
            state['lake_version'] = run(['lake', '--version'], mathlib, pass_fds=fds).strip()
            version = toolchain.strip().rsplit(':v', 1)[-1]
            if not state['lean_version'].startswith(f'Lean (version {version},'):
                raise RuntimeError('Executing compiler version differs from pinned toolchain')
            for module in ordered:
                rel = Path(module.replace('.', '/'))
                dest = (lib / rel).with_suffix('.olean')
                dest.parent.mkdir(parents=True, exist_ok=True)
                command = ['lean']
                if module in TARGETS:
                    command.append('-DwarningAsError=true')
                command.extend(['-o', str(dest), str((src / rel).with_suffix('.lean'))])
                output = run(command, src, env, out / (module + '.log'), fds)
                state['modules'].append({'module': module, 'status': 'passed',
                                         'warnings': output.count('warning:')})
                print('CHECK', module, 'passed', flush=True)
            audit = src / 'LieJordanKernelAudit.lean'
            audit.write_text(audit_source(ordered))
            evidence = run(['lean', str(audit)], src, env, out / 'axioms.log', fds)
            counts = parse_audit_output(evidence, ordered)
            state.update(audited_declarations=sum(counts.values()), module_counts=counts)
            lake_dir = out / 'lake'
            make_lake_package(lake_dir, src, mathlib, toolchain)
            run(['lake', 'build', *TARGETS], lake_dir,
                log=out / 'lake-build.log', pass_fds=fds)
            state['isolated_lake_build'] = 'passed'
            for module, digest in state['source_sha256'].items():
                current = ROOT / 'lean' / (module.replace('.', '/') + '.lean')
                if hashlib.sha256(current.read_bytes()).hexdigest() != digest:
                    raise RuntimeError('Source changed during verification: ' + module)
                copied = src / (module.replace('.', '/') + '.lean')
                if hashlib.sha256(copied.read_bytes()).hexdigest() != digest:
                    raise RuntimeError('Copied source changed during verification: ' + module)
            assert_clean_dependency(mathlib)
            if run(['git', 'rev-parse', 'HEAD'], mathlib).strip() != pin:
                raise RuntimeError('Mathlib revision changed during verification')
            native_manifest = json.loads((mathlib / 'lake-manifest.json').read_text())
            for package in native_manifest['packages']:
                dependency = mathlib / native_manifest['packagesDir'] / package['name']
                assert_clean_dependency(dependency)
                if run(['git', 'rev-parse', 'HEAD'], dependency).strip() != package['rev']:
                    raise RuntimeError('Dependency revision changed during verification: ' + package['name'])
            state['status'] = 'passed'
            print(f'PASSED {len(ordered)} modules; {sum(counts.values())} audited declarations',
                  flush=True)
    except Exception as error:
        state.update(status='failed', error=str(error))
        raise
    finally:
        (out / 'status.json').write_text(json.dumps(state, indent=2) + '\n')


if __name__ == '__main__':
    main()
