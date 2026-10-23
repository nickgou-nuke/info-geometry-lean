"""Native reviewed65 verifier, using intact native caches.

Local kernel-check results and clean-release eligibility are separate. This is
not fresh-build, reproducible-cache, or hermetic/network-isolation certification.
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

def source_files(directory: Path) -> dict:
    """Actual source bytes, including ignored files; exclude generated cache dirs.

    This is source stability evidence, not a proof of all inputs read by Lake.
    Symlink files bind link text and resolved bytes; symlink dirs fail explicitly.
    """
    result = {}
    def unreadable(error):
        raise error
    if not directory.exists():
        return result
    for parent, dirs, files in os.walk(directory, followlinks=False, onerror=unreadable):
        parent = Path(parent)
        for name in list(dirs):
            if name in {'.git', '.lake', '__pycache__'}:
                dirs.remove(name)
            else:
                require(not (parent / name).is_symlink(), f'Unbound source directory symlink: {parent / name}')
        for name in files:
            if name == '.git' or name.endswith(('.pyc', '.pyo')):
                continue
            path = parent / name
            require(path.is_file(), f'Unreadable/special source: {path}')
            result[str(path.relative_to(directory))] = {
                'sha256': sha256_file(path),
                'link': os.readlink(path) if path.is_symlink() else None,
                'resolved': str(path.resolve()) if path.is_symlink() else None}
    return result


def checkout_status(directory: Path, expected: str | None) -> dict:
    """Report dirty/mismatched identity without blocking a local kernel check."""
    row = {'expected': expected, 'head': None, 'status': None, 'nested': {}, 'clean': False}
    try:
        require((directory / '.git').exists(), f'Missing checkout: {directory}')
        require(git(directory, 'rev-parse', '--show-toplevel').strip() == str(directory),
                f'Not a checkout root: {directory}')
        row['head'] = git(directory, 'rev-parse', 'HEAD').strip()
        row['status'] = git(directory, 'status', '--porcelain', '--untracked-files=all')
        for entry in git(directory, 'ls-files', '--stage', '-z').split('\0'):
            if not entry:
                continue
            meta, relative = entry.split('\t', 1)
            mode, revision, stage = meta.split()
            require(stage == '0', f'Unmerged entry: {directory / relative}')
            if mode == '160000':
                row['nested'][relative] = checkout_status(contained_path(directory, relative), revision)
        row['clean'] = (not row['status'] and row['head'] == expected and
                        all(p['clean'] for p in row['nested'].values()))
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        row['error'] = repr(error)
    return row


def snapshot(root: Path) -> dict:
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    preflight = path_package_report(root)
    packages, seen = [], set()
    for item in manifest['packages']:
        name = item['name'].removeprefix('«').removesuffix('»')
        require(name not in seen and name not in ('', '.', '..') and
                '/' not in name and '\\' not in name, 'Invalid package name')
        seen.add(name)
        if item['type'] == 'git':
            checkout = contained_path(contained_path(root, manifest['packagesDir']), name)
            identity = checkout_status(checkout, item['rev'])
            package = contained_path(checkout, item['subDir']) if item.get('subDir') else checkout
        elif item['type'] == 'path':
            checkout = package = contained_path(root, item['dir'])
            path_row = next(p for p in preflight['packages'] if p['name'] == item['name'])
            if path_row['source_kind'] == 'gitlink':
                identity = checkout_status(checkout, path_row['pinned_commit'])
            else:
                status = git(root, 'status', '--porcelain', '--untracked-files=all', '--', item['dir'])
                # Nested path gitlinks are visible in the recorded status; no
                # clean-release claim until their identities have been checked.
                nested = any(x.startswith('160000 ') for x in
                             git(root, 'ls-files', '--stage', '--', item['dir']).splitlines())
                identity = {'status': status, 'clean': path_row['ok'] and not status and not nested,
                            'nested_gitlinks_unchecked': nested}
        else:
            raise RuntimeError(f'Unsupported manifest dependency type: {item}')
        packages.append({'name': name, 'entry': item, 'checkout': str(checkout),
                         'package': str(package), 'identity': identity,
                         'sources': source_files(checkout)})
    sources = {p: source_files(root / p) for p in ('lean', 'tools', 'proofs')}
    configs = {p: sha256_file(root / p) for p in
               ('lean-toolchain', 'lakefile.lean', 'lake-manifest.json', '.gitmodules')}
    root_status = git(root, 'status', '--porcelain', '--untracked-files=all')
    return {'revision': preflight['revision'], 'root_status': root_status,
            'configs': configs, 'manifest': manifest, 'path_preflight': preflight,
            'sources': sources, 'packages': packages,
            'clean_release_eligible': not root_status and preflight['ok'] and
                all(p['identity']['clean'] for p in packages)}



def require_materialized_dependencies(state: dict) -> None:
    """Prevent Lake from materializing missing or wrong-revision dependencies.

    Dirty sources at the pinned revision remain eligible for local checks only.
    This checks availability, not reproducibility of existing build artifacts.
    """
    for package in state['packages']:
        entry = package['entry']
        root = Path(package['package'])
        require(root.is_dir(), f"Missing package directory: {root}")
        config = contained_path(root, entry.get('configFile', 'lakefile.lean'))
        require(config.is_file(), f"Missing package configuration: {config}")
        if entry['type'] == 'git':
            identity = package['identity']
            require(identity.get('head') == entry['rev'],
                    f"Missing or wrong-revision dependency: {package['name']}")


def safe_output(root: Path, output: Path) -> Path:
    candidate = output if output.is_absolute() else root / output
    require('..' not in candidate.parts, 'Output traversal')
    relative = candidate.relative_to(root)
    require(len(relative.parts) == 3 and relative.parts[:2] == ('scratch', 'native_reviewed_runs'),
            'Output must be scratch/native_reviewed_runs/<unique-run>')
    require(not candidate.exists(), 'Output already exists')
    for path in (candidate, *candidate.parents):
        if path == root:
            break
        require(not path.is_symlink(), f'Symlink output ancestor: {path}')
    require(subprocess.run(['git', 'check-ignore', '--no-index', '--', str(relative)],
            cwd=root, capture_output=True).returncode == 0, 'Output must be ignored')
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    providers = [contained_path(root, manifest['packagesDir'])] + [
        contained_path(root, p['dir']) for p in manifest['packages'] if p['type'] == 'path']
    require(not any(candidate.is_relative_to(p) or p.is_relative_to(candidate) for p in providers),
            'Output overlaps dependency provider')
    return candidate


def run_native(root: Path, output: Path, *, wait: bool = False,
               clean_release: bool = False) -> dict:
    root = root.resolve()
    require(Path.cwd().resolve() == root, 'Run from native repository root')
    output = safe_output(root, output)
    targets = validate_targets(json.loads((root / 'tools/quality/reviewed_prs_20260921.json').read_text())['targets'])
    require(tuple(targets) == EXPECTED_TARGETS, 'Exact ordered65 selection must be promoted; no subsetting')
    roles = validate_roles(targets)
    output.mkdir(parents=True, exist_ok=False)
    report = {'local_kernel_status': 'failed', 'clean_release_status': 'failed',
              'mode': 'native', 'targets': targets, 'commands': [],
              'scope': 'Native cached build plus fresh command audits and probe; not fresh/reproducible cache certification'}
    try:
        with BuildLock(DEFAULT_BUILD_LOCK_PATH, 'native-reviewed65-v3', block=wait) as lock:
            idle()
            before = snapshot(root)
            report['before'] = before
            require_materialized_dependencies(before)
            # Provenance failures are recorded, not repaired or concealed. Native
            # build may fail naturally for missing sources/configs. Dirty sources
            # can yield local-only results, never clean-release acceptance.
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
            report['lean_version'] = verify_version((root / 'lean-toolchain').read_text(), banner)
            report['lake_version'] = runner(['lake', '--version']).stdout.strip()
            report['lean_path'] = runner(['lake', 'env', 'printenv', 'LEAN_PATH']).stdout.strip()
            runner(lake_build_command(targets))
            for module in roles:
                runner(['lake', 'env', 'lean', str(root / 'lean' / (module.replace('.', '/') + '.lean'))])
            audit = output / 'ReviewedPRsAudit.lean'
            audit.write_text(audit_source(targets, roles))
            probe = root / 'proofs/PolarizedShearSpinAudit.lean'
            contexts = {str(p): build_lean_context_manifest(root, p, runner=runner) for p in (audit, probe)}
            report['module_counts'] = parse_audit_output(
                runner(['lake', 'env', 'lean', str(audit)]).stdout, targets, roles)
            runner(['lake', 'env', 'lean', str(probe)])
            for source in (audit, probe):
                require(build_lean_context_manifest(root, source, runner=runner) == contexts[str(source)],
                        'Audit/probe context drift')
            report['contexts'] = contexts
            check_command_sources(root / 'lean', targets, roles)
            after = snapshot(root)
            report['after'] = after
            require(after == before, 'Source/config/dependency identity changed during verification')
            report['local_kernel_status'] = 'passed'
            if before['clean_release_eligible']:
                report['clean_release_status'] = 'passed'
            if clean_release:
                require(report['clean_release_status'] == 'passed',
                        'Local kernel checks passed; clean release failed: see dependency/root status')
    except BaseException as error:
        report['error'] = repr(error)
        raise
    finally:
        (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report
