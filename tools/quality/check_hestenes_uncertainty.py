#!/usr/bin/env python3
"""Check the exact Hestenes uncertainty source closure and all owned declarations.

Sources are resolved from lean/, the repository root (including proofs/),
lib/InfoGeometryCore/, and the manifest-pinned LeanArchitect checkout. Every
resolved source dependency is compiled; inherited failures are recorded rather
than replaced by stubs or a smaller import surface. Mathlib and its native
dependencies use their pinned, already initialized cache.

This is a scoped closure check, not a root Lake workspace certificate.
--list-native only discovers source imports; it never starts Lean or Lake.
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
from tools.quality.reviewed_audit_source import audit_source, parse_audit_output, validate_targets

TARGETS = [
    'InfoGeometry.Krein.InternalPhaseGram',
    'InfoGeometry.Krein.PhaseLinearObservableCommutator',
    'InfoGeometry.Canonical.PhaseObservableUncertainty',
    'InfoGeometry.Canonical.CenteredOperatorialUncertainty',
    'InfoGeometry.Canonical.FiniteHestenesHilbertSchmidtStandardForm',
    'InfoGeometry.Canonical.Cl11GNSRealDoubledKreinBridge',
    'InfoGeometry.Canonical.HestenesRightPhaseUncertainty',
]
CACHE_PREFIXES = {
    'Mathlib', 'Batteries', 'Aesop', 'Qq', 'Cli', 'ProofWidgets',
    'LeanSearchClient', 'Plausible', 'ImportGraph',
}
NATIVE_PREFIXES = CACHE_PREFIXES | {'Lean', 'Std', 'Init', 'Lake'}
LEAN_HEADER = (
    '/-\nCopyright (c) 2026 InfoGeometry Authors. All rights reserved.\n'
    'Released under Apache 2.0 license as described in the file LICENSE.\n'
    'Authors: InfoGeometry Engine Contributors\n-/\n\n'
)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked(command, cwd, **kwargs):
    result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, **kwargs)
    if result.returncode:
        raise RuntimeError(f'{command!r}: exit {result.returncode}\n{result.stdout}')
    return result.stdout.strip()


def verify_dependencies(mathlib, architect, pins, toolchain, pass_fds=()):
    for directory, name in [(mathlib, 'mathlib'), (architect, 'LeanArchitect')]:
        if checked(['git', 'rev-parse', 'HEAD'], directory, pass_fds=pass_fds) != pins[name]:
            raise RuntimeError(name + ' source differs from the root manifest pin')
        checked(['git', 'diff', '--exit-code', 'HEAD', '--'], directory, pass_fds=pass_fds)
    if (mathlib / 'lean-toolchain').read_text().strip() != toolchain:
        raise RuntimeError('Mathlib toolchain differs from the root toolchain')


def closure(architect, targets):
    """Return every actual source dependency and the native-cache boundary."""
    roots = [ROOT / 'lean', ROOT, ROOT / 'lib/InfoGeometryCore', architect]
    sources, dependencies, ordered, active, native = {}, {}, [], set(), set()

    def visit(module):
        if module in dependencies or module in native:
            return
        if module in active:
            raise RuntimeError('Import cycle at ' + module)
        relative = Path(module.replace('.', '/') + '.lean')
        source = next((root / relative for root in roots if (root / relative).is_file()), None)
        if source is None:
            if module.split('.')[0] not in NATIVE_PREFIXES:
                raise RuntimeError('Unresolved actual source import: ' + module)
            native.add(module)
            return
        active.add(module)
        children = []
        for line in source.read_text().splitlines():
            match = re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)', line)
            if match:
                for child in match[1].split('--', 1)[0].split():
                    visit(child)
                    if child not in native and child not in children:
                        children.append(child)
        active.remove(module)
        sources[module], dependencies[module] = source, children
        ordered.append(module)

    for target in targets:
        visit(target)
        if target not in sources:
            raise RuntimeError('Selected owner has no actual source: ' + target)
    return sources, dependencies, ordered, native


def artifacts_for(destination, output):
    return {str(path.relative_to(output)): digest(path)
            for path in destination.parent.glob(destination.stem + '.olean*') if path.is_file()}


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mathlib-root', type=Path, required=True)
    parser.add_argument('--architect-root', type=Path, required=True)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--output', type=Path,
                        help='Isolated evidence/build directory; required except with --list-native')
    parser.add_argument('--target', action='append', help='Override the seven default owners')
    parser.add_argument('--incremental', action='store_true')
    parser.add_argument('--recheck-targets', action='store_true',
                        help='Recompile selected owners even when exact dependency outputs can be reused')
    parser.add_argument('--list-native', action='store_true',
                        help='Print native cache module names without invoking Lean or Lake')
    args = parser.parse_args()
    targets = validate_targets(args.target or TARGETS)
    mathlib, architect = args.mathlib_root.resolve(), args.architect_root.resolve()
    if not args.list_native and args.output is None:
        parser.error('--output is required for verification')

    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    packages = {package['name']: package for package in manifest['packages']}
    pins = {name: packages[name]['rev'] for name in ('mathlib', 'LeanArchitect')}
    if any(re.fullmatch(r'[0-9a-f]{40}', pin) is None for pin in pins.values()):
        raise RuntimeError('Dependencies require exact manifest commit pins')
    toolchain = (ROOT / 'lean-toolchain').read_text().strip()

    if args.list_native:
        verify_dependencies(mathlib, architect, pins, toolchain)
        _, _, _, native = closure(architect, targets)
        # Cache.IO accepts module names for external packages; their relative
        # paths (for example Batteries/...lean) do not exist at Mathlib's root.
        print('\n'.join(sorted(m for m in native if m.split('.')[0] in CACHE_PREFIXES)))
        return

    output = args.output.resolve()
    if any(output == root or output in root.parents for root in (ROOT, mathlib, architect)):
        raise RuntimeError('Output must not contain or replace a source checkout')
    if any(root in output.parents for root in (mathlib, architect)):
        raise RuntimeError('Output must be outside dependency checkouts')
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / 'report.json'
    report = {
        'status': 'pending', 'targets': targets, 'modules': [], 'audit_required': True,
        'scope': 'Exact source closure and native axiom audit of all selected-owner declarations',
        'driver_sha256': digest(Path(__file__)),
        'flags': {'incremental': args.incremental, 'recheck_targets': args.recheck_targets},
        'dependency_pins': pins, 'toolchain': toolchain,
    }
    try:
        previous = json.loads(report_path.read_text()) if args.incremental and report_path.exists() else {}
        report['prior_report_sha256'] = digest(report_path) if previous else None
        helper_paths = ['tools/build_lock.py', 'tools/quality/reviewed_audit_source.py']
        helpers = {path: digest(ROOT / path) for path in helper_paths}
        inputs = {path: digest(ROOT / path) for path in ['lean-toolchain', 'lake-manifest.json']}
        report.update(maintained_helper_sha256=helpers, configuration_sha256=inputs,
                      git_head=checked(['git', 'rev-parse', 'HEAD'], ROOT))
        verify_dependencies(mathlib, architect, pins, toolchain)
        report['architect_declared_toolchain'] = (architect / 'lean-toolchain').read_text().strip()
        sources, dependencies, ordered, native = closure(architect, targets)
        source, library = output / 'src', output / 'lib'
        source.mkdir(exist_ok=True)
        library.mkdir(exist_ok=True)
        (source / 'lean-toolchain').write_text(toolchain + '\n')
        hashes, fingerprints = {}, {}
        for module in ordered:
            destination = source / (module.replace('.', '/') + '.lean')
            destination.parent.mkdir(parents=True, exist_ok=True)
            data = sources[module].read_bytes()
            destination.write_bytes(data)
            hashes[module] = hashlib.sha256(data).hexdigest()
            payload = [module, hashes[module], toolchain, pins, inputs, helpers,
                       report['driver_sha256'], [fingerprints[d] for d in dependencies[module]]]
            fingerprints[module] = hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()
        report.update(source_sha256=hashes, source_paths={m: str(p) for m, p in sources.items()},
                      fingerprints=fingerprints, dependencies=dependencies, native_imports=sorted(native))
        report_path.write_text(json.dumps(report, indent=2) + '\n')
        lean = shutil.which(args.lean)
        if lean is None:
            raise RuntimeError('Pinned Lean executable not found: ' + args.lean)
        # Preserve an elan proxy's executable name; resolving its symlink to
        # `elan` would change which command is executed.
        lean = os.path.abspath(lean)
        print(f'Waiting for shared lock; {len(ordered)} exact-source modules', flush=True)
        with BuildLock(DEFAULT_BUILD_LOCK_PATH, 'hestenes-uncertainty', block=True) as lock:
            descriptors = (lock.fileno(),)
            active = checked(['ps', '-eo', 'comm='], ROOT, pass_fds=descriptors).splitlines()
            if any(name.strip() in {'lean', 'lake', 'leanc'} for name in active):
                raise RuntimeError('Concurrent Lean compiler detected')
            version = checked([lean, '--version'], source, pass_fds=descriptors)
            match = re.search(r'\bversion ([^, ]+)', version)
            if match is None or match[1] != toolchain.rsplit(':v', 1)[-1]:
                raise RuntimeError('Lean does not match the root toolchain')
            report['lean_version'] = version
            report['lake_version'] = checked([str(Path(lean).with_name('lake')), '--version'],
                                             source, pass_fds=descriptors)
            prefix = Path(checked([lean, '--print-prefix'], source, pass_fds=descriptors))
            search = [library, *sorted((mathlib / '.lake/packages').glob('*/.lake/build/lib/lean')),
                      mathlib / '.lake/build/lib/lean', prefix / 'lib/lean']
            environment = {**os.environ, 'LEAN_PATH': os.pathsep.join(map(str, search))}
            (output / 'environment.json').write_text(json.dumps({
                'LEAN_PATH': environment['LEAN_PATH'], 'lean': lean,
                'mathlib_root': str(mathlib), 'architect_root': str(architect)}, indent=2) + '\n')
            previous_modules = {m['module']: m for m in previous.get('modules', [])}
            failed = set()
            for module in ordered:
                blocked = [dep for dep in dependencies[module] if dep in failed]
                if blocked:
                    failed.add(module)
                    report['modules'].append({'module': module, 'returncode': None, 'blocked_by': blocked})
                    print('BLOCKED', module, blocked, flush=True)
                    continue
                relative = Path(module.replace('.', '/'))
                destination = (library / relative).with_suffix('.olean')
                destination.parent.mkdir(parents=True, exist_ok=True)
                old = previous_modules.get(module, {})
                artifacts = old.get('artifacts', {})
                if (args.incremental and not (args.recheck_targets and module in targets)
                        and previous.get('lean_version') == version
                        and previous.get('fingerprints', {}).get(module) == fingerprints[module]
                        and old.get('returncode') == 0
                        and str(destination.relative_to(output)) in artifacts
                        and artifacts_for(destination, output) == artifacts):
                    report['modules'].append({**old, 'reused': True})
                    print('REUSE', module, flush=True)
                    continue
                result = subprocess.run([lean, '-o', str(destination),
                                         str((source / relative).with_suffix('.lean'))],
                    cwd=source, env=environment, pass_fds=descriptors, text=True,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                (output / (module + '.log')).write_text(result.stdout)
                warnings = len(re.findall(r'\bwarning:', result.stdout))
                report['modules'].append({
                    'module': module, 'returncode': result.returncode, 'warnings': warnings,
                    'artifacts': artifacts_for(destination, output) if result.returncode == 0 else {},
                    'reused': False})
                report_path.write_text(json.dumps(report, indent=2) + '\n')
                print('CHECK', module, 'exit', result.returncode, 'warnings', warnings, flush=True)
                if result.returncode:
                    failed.add(module)
                    print(result.stdout, flush=True)
            if failed:
                raise RuntimeError('Source closure failed or blocked: ' + ', '.join(sorted(failed)))
            if any(m.get('warnings', 0) for m in report['modules'] if m['module'] in targets):
                raise RuntimeError('Selected-owner warnings must be resolved')
            audit = source / 'HestenesUncertaintyOwnerAudit.lean'
            audit.write_text(LEAN_HEADER + audit_source(targets))
            report['audit_source_sha256'] = digest(audit)
            result = subprocess.run([lean, str(audit)], cwd=source, env=environment,
                pass_fds=descriptors, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (output / 'axioms.log').write_text(result.stdout)
            if result.returncode or re.search(r'\bwarning:', result.stdout):
                raise RuntimeError('Native owner audit failed; see axioms.log')
            counts = parse_audit_output(result.stdout, targets)
            report.update(declaration_counts=counts, audited_declarations=sum(counts.values()),
                          axioms=re.findall(r'^AUDIT_AXIOMS: (.*)$', result.stdout, re.MULTILINE))
            for module, expected in hashes.items():
                if digest(sources[module]) != expected:
                    raise RuntimeError('Source changed during verification: ' + module)
                if digest(source / (module.replace('.', '/') + '.lean')) != expected:
                    raise RuntimeError('Copied source changed during verification: ' + module)
            if digest(Path(__file__)) != report['driver_sha256']:
                raise RuntimeError('Verification driver changed during verification')
            for path, expected in {**inputs, **helpers}.items():
                if digest(ROOT / path) != expected:
                    raise RuntimeError('Verification configuration/helper changed: ' + path)
            if checked(['git', 'rev-parse', 'HEAD'], ROOT, pass_fds=descriptors) != report['git_head']:
                raise RuntimeError('Repository revision changed during verification')
            verify_dependencies(mathlib, architect, pins, toolchain, pass_fds=descriptors)
            report['status'] = 'passed'
            print('PASSED', counts, report['axioms'], flush=True)
    except Exception as error:
        report.update(status='failed', error=str(error))
        raise
    finally:
        report_path.write_text(json.dumps(report, indent=2) + '\n')
        evidence = [report_path, *sorted(output.glob('*.log'))]
        for relative in ('environment.json', 'native-imports.txt', 'src/HestenesUncertaintyOwnerAudit.lean'):
            path = output / relative
            if path.is_file():
                evidence.append(path)
        (output / 'evidence-sha256.json').write_text(json.dumps(
            {str(path.relative_to(output)): digest(path) for path in evidence}, indent=2) + '\n')


if __name__ == '__main__':
    main()
