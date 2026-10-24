"""Unexecuted native reviewed65 candidate; call from the optional checker branch.

Requires clean pinned sources, cold root/Architect/config artifacts and trusted
receipts for warm dependency artifacts. Network isolation is an external CI control.
Unexecuted proposal; never removes artifacts or repairs dependencies.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import traceback

from tools.build_lock import BuildLock, DEFAULT_BUILD_LOCK_PATH
from tools.infra.build import lake_build_command
from tools.infra.check_runtime_acceptance import idle, require
from tools.infra.ci_bootstrap import contained_path, git, path_package_report, verify_version
from tools.infra.pantograph_environment import build_lean_context_manifest, sha256_file
from tools.quality.reviewed_audit_source import (
    audit_source, check_command_sources, parse_audit_output, validate_roles, validate_targets,
)


# Reviewed upstream 81867ee217620005c5c18c4cb78b15f8d24f68db, exact order.
EXPECTED_TARGETS = (
    'InfoGeometry.Algebra.CuntzClifford22',
    'InfoGeometry.Algebra.CuntzClifford22Audit',
    'InfoGeometry.Algebra.CuntzClockObstructions',
    'InfoGeometry.Algebra.CuntzMatrixUnitRepresentation',
    'InfoGeometry.Algebra.RegularBimoduleWeylObstruction',
    'InfoGeometry.Algebraic.Fitting',
    'InfoGeometry.Analysis.IntervalBarrierPotential',
    'InfoGeometry.Analysis.LogHomogeneousPotential',
    'InfoGeometry.Analysis.TwoSheetPoleCancellation',
    'InfoGeometry.Canonical.AharonovKreinWeakValueBridge',
    'InfoGeometry.Canonical.AnomalyStrainRotation',
    'InfoGeometry.Canonical.AnomalyStrainRotationWitness',
    'InfoGeometry.Canonical.CuntzCliffordGaugeChain',
    'InfoGeometry.Canonical.DiracKahlerSplitCurvature',
    'InfoGeometry.Canonical.EnstrophyDivergence',
    'InfoGeometry.Canonical.FiniteSuperchargePairing',
    'InfoGeometry.Canonical.KreinFlowConservation',
    'InfoGeometry.Canonical.KreinSeamEvolution',
    'InfoGeometry.Canonical.NavierStokesPolarizedTransfers',
    'InfoGeometry.Canonical.NavierStokesShearReconstruction',
    'InfoGeometry.Canonical.PolarizedShearSpinEvolution',
    'InfoGeometry.Canonical.PolarizedShearSpinFrame',
    'InfoGeometry.Canonical.PolarizedShearSpinSolution',
    'InfoGeometry.Canonical.QuantumSpinNavierStokes',
    'InfoGeometry.Canonical.ReciprocalShearFlow',
    'InfoGeometry.Canonical.SpinorHydrodynamicReadout',
    'InfoGeometry.Canonical.SpinorReadoutOscillation',
    'InfoGeometry.Canonical.SpinorReadoutRegularity',
    'InfoGeometry.Canonical.SquareZeroStrainRotation',
    'InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator',
    'InfoGeometry.Canonical.TwoSheetResiduePairing',
    'InfoGeometry.Canonical.TwoStateMomentumShear',
    'InfoGeometry.Canonical.TwoStateNavierStokesReconstruction',
    'InfoGeometry.Canonical.WeakValueCylinderTransport',
    'InfoGeometry.Canonical.WeakValueEnstrophy',
    'InfoGeometry.Canonical.WeakValueForcedShear',
    'InfoGeometry.Canonical.WeakValueKreinBoundary',
    'InfoGeometry.Canonical.WeakValueKreinGeometry',
    'InfoGeometry.Canonical.WeakValuePoleBounds',
    'InfoGeometry.Canonical.WeakValuePoleCriterion',
    'InfoGeometry.Canonical.WeakValuePoleExamples',
    'InfoGeometry.Canonical.WeakValueReconstructionChecks',
    'InfoGeometry.Canonical.WeakValueSpatialReconstruction',
    'InfoGeometry.Clifford.CuntzSplitClifford22',
    'InfoGeometry.Exceptional.CubicJordanQuadraticLaws',
    'InfoGeometry.Exceptional.FreudenthalChargeLinear',
    'InfoGeometry.Exceptional.FreudenthalLogPotential',
    'InfoGeometry.Geometry.AssociativeGaugeConnection',
    'InfoGeometry.Geometry.FlatSplitQuaternionFamily',
    'InfoGeometry.Geometry.FlatSplitQuaternionPotential',
    'InfoGeometry.Geometry.QuadraticPotentialCalculus',
    'InfoGeometry.Krein.TransitionWeakValue',
    'InfoGeometry.Krein.TransitionWeakValueAudit',
    'InfoGeometry.Krein.TransitionWeakValueExamples',
    'InfoGeometry.Modular.KreinPotentialTrace',
    'InfoGeometry.Meta.FiniteTemperleyLiebTrace',
    'InfoGeometry.Canonical.DrazinShellCascade',
    'InfoGeometry.Canonical.DrazinInterShellHodge',
    'InfoGeometry.Core.DiracPeirceSuperalgebra',
    'InfoGeometry.Core.SupercolorMultiplication',
    'InfoGeometry.Routing.AttentionReadoutCompression',
    'InfoGeometry.MassSpectrometry.MolecularIdentifiabilityBridge',
    'InfoGeometry.Algebra.CuntzTensorQuotientPositivityObstruction',
    'InfoGeometry.Canonical.MajoranaCoefficientAction',
    'InfoGeometry.Canonical.MajoranaPfaffian4',
)

def no_symlink_path(path: Path) -> None:
    for component in (path, *path.parents):
        require(not component.is_symlink(), f'Symlink path component: {component}')


def provider_path(root: Path, relative: str) -> Path:
    no_symlink_path(root / relative)
    return contained_path(root, relative)


def files_under(directory: Path, excluded=()) -> dict[str, str]:
    """Bind ignored files too; reject symlinks rather than follow unbound targets."""
    no_symlink_path(directory)
    if not directory.exists():
        return {}
    require(directory.is_dir(), f'Expected inventory directory: {directory}')
    excluded = set(excluded)
    result = {}
    def unreadable(error):
        raise error
    for parent, dirs, files in os.walk(directory, followlinks=False, onerror=unreadable):
        parent = Path(parent)
        for name in list(dirs) + files:
            path = parent / name
            if name == '.git' or path in excluded:
                if name in dirs:
                    dirs.remove(name)
                continue
            require(not path.is_symlink(), f'Unbound symlink: {path}')
            if name in files:
                require(path.is_file(), f'Unsupported special file: {path}')
                result[str(path.relative_to(directory))] = sha256_file(path)
    return result


def clean_checkout(directory: Path, pin: str) -> dict:
    require((directory / '.git').exists(), f'Missing checkout: {directory}')
    require(git(directory, 'rev-parse', '--show-toplevel').strip() == str(directory),
            f'Not a checkout root: {directory}')
    require(git(directory, 'rev-parse', 'HEAD').strip() == pin, f'Wrong pin: {directory}')
    require(not git(directory, 'status', '--porcelain', '--untracked-files=all').strip(),
            f'Dirty checkout: {directory}')
    nested = {}
    for entry in git(directory, 'ls-files', '--stage', '-z').split('\0'):
        if not entry:
            continue
        meta, relative = entry.split('\t', 1)
        mode, revision, stage = meta.split()
        require(stage == '0', f'Unmerged index: {directory}')
        if mode == '160000':
            child = provider_path(directory, relative)
            nested[relative] = clean_checkout(child, revision)
    return {'head': pin, 'nested_gitlinks': nested}


def source_identity(root: Path) -> dict:
    preflight = path_package_report(root)
    require(preflight['ok'], 'ci_bootstrap path provenance failed: ' + repr(preflight))
    require(not git(root, 'status', '--porcelain', '--untracked-files=all').strip(),
            'Native acceptance requires a clean committed checkout')
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    packages = provider_path(root, manifest['packagesDir'])
    rows, seen = [], set()
    for item in manifest['packages']:
        name = item['name'].removeprefix('«').removesuffix('»')
        require(name not in seen and name not in ('', '.', '..') and
                '/' not in name and '\\' not in name, 'Invalid/duplicate package identity')
        seen.add(name)
        if item['type'] == 'git':
            checkout = provider_path(packages, name)
            provenance = clean_checkout(checkout, item['rev'])
            package = provider_path(checkout, item['subDir']) if item.get('subDir') else checkout
        elif item['type'] == 'path':
            checkout = package = provider_path(root, item['dir'])
            if (checkout / '.git').exists():
                pinned = next(p['pinned_commit'] for p in preflight['packages'] if p['name'] == item['name'])
                provenance = clean_checkout(checkout, pinned)
            else:
                # In-tree path sources use the root commit; reject nested gitlinks
                # here unless represented as a separately reviewed path checkout.
                listing = git(root, 'ls-files', '--stage', '--', item['dir'])
                require(not any(x.startswith('160000 ') for x in listing.splitlines()),
                        f'In-tree nested gitlink needs explicit path provider: {name}')
                provenance = {'root_commit': preflight['revision']}
        else:
            raise RuntimeError(f'Unsupported dependency type: {item}')
        require(not checkout.is_symlink() and not package.is_symlink(), 'Symlink package root')
        config = provider_path(package, item.get('configFile', 'lakefile.lean'))
        require(config.is_file() and not config.is_symlink(), f'Missing/symlink config: {name}')
        excluded = (package / '.lake/build', root / '.lake/config')
        rows.append({'name': name, 'checkout': str(checkout), 'directory': str(package),
                     'entry': item, 'provenance': provenance,
                     'sources': files_under(checkout, excluded)})
    # Root module/helper/probe providers include ignored files; unrelated scratch
    # trees are not declared source providers. Arbitrary build inputs remain a CI
    # sandbox policy responsibility, not a claim of this inventory.
    sources = {p: files_under(root / p) for p in ('lean', 'tools', 'proofs')}
    configs = {p: sha256_file(provider_path(root, p)) for p in
               ('lakefile.lean', 'lake-manifest.json', 'lean-toolchain', '.gitmodules')}
    return {'revision': preflight['revision'], 'path_preflight': preflight,
            'packages': rows, 'sources': sources, 'configs': configs}


def cache_preflight(root: Path, identity: dict, receipt_path: Path | None,
                    trusted_digest: str | None) -> None:
    # Workspace LoadConfig.configDir is .lake/config/<pkgIdx>, including deps.
    require(not files_under(root / '.lake/config'), 'Unproven workspace config cache')
    require(not files_under(root / '.lake/build'), 'Root artifacts must be cold')
    receipt = None
    if receipt_path is not None:
        require(bool(trusted_digest) and sha256_file(receipt_path) == trusted_digest,
                'Dependency receipt differs from externally trusted digest')
        receipt = json.loads(receipt_path.read_text())
        require(receipt['schema'] == 'reviewed-native-dependency-cache-v1', 'Receipt schema')
        require(receipt['configs'] == identity['configs'], 'Receipt root/toolchain mismatch')
    else:
        require(trusted_digest is None, 'Digest supplied without receipt')
    accepted = set()
    for row in identity['packages']:
        artifacts = files_under(Path(row['directory']) / '.lake/build')
        if row['name'] == 'LeanArchitect':
            require(not artifacts, 'Architect artifacts must be cold at clean exact pin')
        elif artifacts:
            require(receipt is not None, f"Unproven dependency cache: {row['name']}")
            record = receipt['packages'].get(row['name'])
            # Paths are made CI-checkout-independent; source bytes and pins are not.
            expected = {k: row[k] for k in ('entry', 'provenance', 'sources')}
            require(record == {'source': expected, 'artifacts': artifacts},
                    f"Dependency cache provenance mismatch: {row['name']}")
            accepted.add(row['name'])
    if receipt is not None:
        require(set(receipt['packages']) == accepted, 'Extra/missing cache receipt entries')


def safe_output(root: Path, output: Path) -> Path:
    # Dedicated ignored run namespace, never a source/dependency/build directory.
    candidate = output if output.is_absolute() else root / output
    require('..' not in candidate.parts, 'Output traversal')
    relative = candidate.relative_to(root)
    require(len(relative.parts) == 3 and relative.parts[:2] == ('scratch', 'native_reviewed_runs'),
            'Output must be scratch/native_reviewed_runs/<unique-run>')
    for path in (candidate, *candidate.parents):
        if path == root:
            break
        require(not path.is_symlink(), f'Symlink output ancestor: {path}')
    require(not candidate.exists(), 'Output already exists')
    result = subprocess.run(['git', 'check-ignore', '--no-index', '--', str(relative)],
                            cwd=root, text=True, capture_output=True)
    require(result.returncode == 0, 'Output must be ignored before creation')
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    providers = [provider_path(root, manifest['packagesDir'])] + [
        provider_path(root, p['dir']) for p in manifest['packages'] if p['type'] == 'path']
    require(not any(candidate.is_relative_to(p) or p.is_relative_to(candidate) for p in providers),
            'Output overlaps dependency provider')
    return candidate


def run_native(root: Path, output: Path, *, wait: bool = False,
               receipt_path: Path | None = None, trusted_cache_digest: str | None = None) -> dict:
    root = root.resolve()
    output = safe_output(root, output)
    require(Path.cwd().resolve() == root, 'Run from native repository root')
    spec = root / 'tools/quality/reviewed_prs_20260921.json'
    targets = validate_targets(json.loads(spec.read_text())['targets'])
    require(tuple(targets) == EXPECTED_TARGETS,
            'Exact ordered reviewed65 selection not promoted or changed; no fallback/subsetting')
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
            cache_preflight(root, before, receipt_path, trusted_cache_digest)
            report['trusted_cache_receipt_sha256'] = trusted_cache_digest
            check_command_sources(root / 'lean', targets, roles)

            def runner(argv, cwd=None, **kwargs):
                unknown = set(kwargs) - {'input', 'check', 'capture_output', 'text'}
                require(not unknown, f'Unsupported runner kwargs: {unknown}')
                require(kwargs.get('text', True) is True and kwargs.get('capture_output', True) is True,
                        'Runner requires captured text')
                require(isinstance(kwargs.get('check', True), bool), 'check must be bool')
                data = kwargs.get('input')
                require(data is None or isinstance(data, str), 'input must be text or None')
                idle()
                argv = list(argv)
                if argv and argv[0] == 'lake':
                    argv[1:1] = ['--offline', '--no-cache']
                label = f"command-{len(report['commands']):04d}"
                row = {'argv': argv, 'cwd': str(cwd or root), 'exit_code': None,
                       'status': 'launching', 'log_prefix': label}
                report['commands'].append(row)
                try:
                    process = subprocess.Popen(argv, cwd=cwd or root, text=True,
                        stdin=subprocess.PIPE if data is not None else subprocess.DEVNULL,
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                        pass_fds=(lock.fileno(),), start_new_session=True)
                except BaseException:
                    row['status'] = 'launch_failed'
                    (output / (label + '.stdout.log')).write_text('')
                    (output / (label + '.stderr.log')).write_text(traceback.format_exc())
                    raise
                interrupted = False
                while True:
                    try:
                        stdout, stderr = process.communicate(input=data)
                        break
                    except KeyboardInterrupt:
                        interrupted = True
                        data = None  # communicate resumes; do not resend stdin
                (output / (label + '.stdout.log')).write_text(stdout)
                (output / (label + '.stderr.log')).write_text(stderr)
                row.update(exit_code=process.returncode, status='exited')
                if interrupted:
                    raise KeyboardInterrupt
                if kwargs.get('check', True):
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
            report['scope'] = 'Native reviewed65 with externally enforced CI sandbox; not network isolation proof'
    except BaseException as error:
        report['error'] = repr(error)
        raise
    finally:
        (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report
