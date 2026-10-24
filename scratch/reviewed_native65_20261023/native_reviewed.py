"""Unexecuted native reviewed65 candidate; call from the optional checker branch.

Requires a clean CI source checkout and cold native build directories. Never
removes artifacts or repairs dependencies. Existing unproven caches fail closed.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess

from tools.build_lock import BuildLock, DEFAULT_BUILD_LOCK_PATH
from tools.infra.build import lake_build_command
from tools.infra.check_runtime_acceptance import idle, require
from tools.infra.ci_bootstrap import contained_path, git, path_package_report, verify_version
from tools.infra.pantograph_environment import build_lean_context_manifest, sha256_file
from tools.quality.reviewed_audit_source import (
    audit_source, check_command_sources, parse_audit_output, validate_roles, validate_targets,
)


def source_identity(root: Path) -> dict:
    """Supplement bootstrap's direct path checks with exact installed git pins.

    Deliberately all manifest packages, not an inferred Mathlib-only closure.
    Unsupported subDir/manifest layouts fail rather than guess provider locations.
    """
    preflight = path_package_report(root)
    require(preflight['ok'], 'ci_bootstrap path provenance failed: ' + repr(preflight))
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    packages = contained_path(root, manifest['packagesDir'])
    rows = []
    seen = set()
    for item in manifest['packages']:
        name = item['name'].removeprefix('«').removesuffix('»')
        require(name not in seen and name not in ('', '.', '..') and
                '/' not in name and '\\' not in name, 'Invalid/duplicate package identity')
        seen.add(name)
        require(not item.get('subDir'), 'subDir requires explicit provider review')
        if item['type'] == 'git':
            directory = contained_path(packages, name)
            require((directory / '.git').exists(), f'Missing package checkout: {name}')
            require(git(directory, 'rev-parse', '--show-toplevel').strip() == str(directory),
                    f'Package is not its own repository: {name}')
            require(git(directory, 'rev-parse', 'HEAD').strip() == item['rev'],
                    f'Package revision differs from manifest: {name}')
            require(not git(directory, 'status', '--porcelain', '--untracked-files=all').strip(),
                    f'Dirty package: {name}')
            # Unknown nested gitlink sources need a separately reviewed provider map.
            require(not any(row.startswith('160000 ') for row in
                            git(directory, 'ls-files', '--stage').splitlines()),
                    f'Nested gitlinks need provenance support: {name}')
        elif item['type'] == 'path':
            directory = contained_path(root, item['dir'])
            require(not git(root, 'status', '--porcelain', '--untracked-files=all',
                            '--', item['dir']).strip(), f'Dirty path package: {name}')
        else:
            raise RuntimeError(f'Unsupported dependency type: {item}')
        config = contained_path(directory, item.get('configFile', 'lakefile.lean'))
        require(config.is_file(), f'Missing native package config: {name}')
        rows.append({'name': name, 'directory': str(directory), 'entry': item,
                     'config_sha256': sha256_file(config)})
    # Require committed native sources; staged/untracked source changes are not CI inputs.
    # Ignored output directories are permitted. Git checks are read-only.
    require(not git(root, 'status', '--porcelain', '--untracked-files=all').strip(),
            'Native acceptance requires a clean committed checkout')
    paths = [p for p in git(root, 'ls-files', '-z').split('\0') if p]
    files = {p: sha256_file(root / p) for p in paths if (root / p).is_file()}
    return {'revision': git(root, 'rev-parse', 'HEAD').strip(),
            'path_preflight': preflight, 'packages': rows, 'source_sha256': files}


def require_cold_builds(root: Path, identity: dict) -> None:
    """No deletion: use a fresh CI checkout, or stop for cache-provenance design."""
    for directory in [root, *(Path(p['directory']) for p in identity['packages'])]:
        build = directory / '.lake' / 'build'
        require(not build.exists() or not any(p.is_file() for p in build.rglob('*')),
                f'Unproven preexisting build artifacts: {build}')
        # Cached Lake configuration is executable too; do not bless dirty-era config.
        require(not any((directory / '.lake').glob('lakefile.olean*')),
                f'Unproven cached Lake configuration: {directory}')


def run_native(root: Path, output: Path, *, wait: bool = False) -> dict:
    root, output = root.resolve(), output.resolve()
    require(Path.cwd().resolve() == root, 'Run from native repository root')
    require(output.is_relative_to(root) and output != root, 'Use fresh in-repo ignored output')
    spec = root / 'tools/quality/reviewed_prs_20260921.json'
    targets = validate_targets(json.loads(spec.read_text())['targets'])
    require(len(targets) == 65, 'Reviewed65 target set changed: explicit contract review required')
    roles = validate_roles(targets)
    output.mkdir(parents=True, exist_ok=False)
    report = {'status': 'failed', 'mode': 'native', 'targets': targets, 'commands': []}
    try:
        with BuildLock(DEFAULT_BUILD_LOCK_PATH, 'native-reviewed65', block=wait) as lock:
            idle()
            require(not any(os.environ.get(k) for k in
                            ('LEAN_PATH', 'LEAN_SRC_PATH', 'LAKE_HOME', 'LEAN_SYSROOT')),
                    'Ambient Lean/Lake path overrides are not accepted')
            before = source_identity(root)
            report['source_identity'] = before
            require_cold_builds(root, before)
            check_command_sources(root / 'lean', targets, roles)

            def runner(argv, cwd=None, **kwargs):
                # Adapter also used by the existing context manifest helper.
                idle()
                argv = list(argv)
                if argv and argv[0] == 'lake':
                    argv[1:1] = ['--offline', '--no-cache']
                process = subprocess.Popen(argv, cwd=cwd or root, text=True,
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    pass_fds=(lock.fileno(),), start_new_session=True)
                interrupted = False
                while True:
                    try:
                        stdout, stderr = process.communicate()
                        break
                    except KeyboardInterrupt:
                        interrupted = True  # retain lock, never kill compiler
                index = len(report['commands'])
                label = f'command-{index:04d}'
                (output / (label + '.stdout.log')).write_text(stdout)
                (output / (label + '.stderr.log')).write_text(stderr)
                report['commands'].append({'argv': list(argv), 'cwd': str(cwd or root),
                    'exit_code': process.returncode, 'log_prefix': label})
                if interrupted:
                    raise KeyboardInterrupt
                require(process.returncode == 0, f'Command failed: {label}')
                return subprocess.CompletedProcess(argv, process.returncode, stdout, stderr)

            banner = runner(['lake', 'env', 'lean', '--version']).stdout
            verify_version((root / 'lean-toolchain').read_text(), banner)
            # No copied closure, external import whitelist, or alternate lakefile.
            command = lake_build_command(targets)
            command[1:1] = ['--rehash']
            runner(command)
            for module in roles:
                runner(['lake', 'env', 'lean', str(root / 'lean' /
                        (module.replace('.', '/') + '.lean'))])
            audit = output / 'ReviewedPRsAudit.lean'
            audit.write_text(audit_source(targets, roles))
            probe = root / 'proofs/PolarizedShearSpinAudit.lean'
            contexts = {}
            for source in (audit, probe):
                context = build_lean_context_manifest(root, source, runner=runner)
                require(not any(p['path'].startswith('absolute:') for p in context['sourceLeanOleans']),
                        'Dependency resolves outside project/toolchain')
                approved_libs = [root / '.lake/build/lib/lean', *(
                    Path(p['directory']) / '.lake/build/lib/lean' for p in before['packages'])]
                for artifact in context['sourceLeanOleans']:
                    if artifact['path'].startswith('project:'):
                        resolved = (root / artifact['path'].removeprefix('project:')).resolve()
                        require(any(resolved.is_relative_to(lib.resolve()) for lib in approved_libs),
                                f'Unexpected project artifact provider: {resolved}')
                contexts[str(source)] = context
            report['module_counts'] = parse_audit_output(
                runner(['lake', 'env', 'lean', str(audit)]).stdout, targets, roles)
            runner(['lake', 'env', 'lean', str(probe)])
            for source in (audit, probe):
                require(build_lean_context_manifest(root, source, runner=runner) == contexts[str(source)],
                        'Audit/probe olean context drift')
            report['contexts'] = contexts
            check_command_sources(root / 'lean', targets, roles)
            require(source_identity(root) == before, 'Source/dependency provenance drift')
            report['status'] = 'passed'
    except BaseException as error:
        report['error'] = repr(error)
        raise
    finally:
        (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report
