"""Reproduce the detector audit and seal a source-hashed mathematical snapshot.

Only repo-owned transitive Lean imports are hashed. Toolchain/manifest hashes
identify dependency configuration; modified dependency worktrees remain an
explicit qualification. No experimental calibration claim is made.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import argparse

ROOT = Path(__file__).resolve().parents[1]
TARGET = 'InfoGeometry.Nuclear.DetectorInformationGeometryAudit'
OUT = ROOT / 'artifacts/detector_theory_seal'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def sources(module, found=None):
    found = {} if found is None else found
    p = ROOT / 'lean' / (module.replace('.', '/') + '.lean')
    if not p.is_file() or module in found:
        return found
    found[module] = p
    for dep in re.findall(r'^import\s+([\w.]+)', p.read_text(), re.M):
        sources(dep, found)
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Check saved seal without rerunning the compiler')
    args = parser.parse_args()
    if args.check:
        manifest = json.loads((OUT / 'manifest.json').read_text())
        for path, digest in manifest['repo_owned_imports_hashed'].items():
            assert sha(ROOT/path) == digest, f'Stale Lean source: {path}'
        for path, digest in manifest['configuration'].items():
            assert sha(ROOT/path) == digest, f'Changed build configuration: {path}'
        for name, evidence in manifest['cas'].items():
            assert sha(ROOT/'scripts'/name) == evidence['sha256'], f'Changed CAS script: {name}'
        assert sha(OUT/'kernel.log') == manifest['kernel_log_sha256'], 'Changed kernel log'
        assert sha(Path(__file__)) == manifest['seal_script_sha256'], 'Changed seal implementation'
        print('SOURCE_SNAPSHOT_CURRENT')
        return
    OUT.mkdir(parents=True, exist_ok=True)
    owners = sources(TARGET)
    before = {str(p.relative_to(ROOT)): sha(p) for p in owners.values()}
    expected = {name for p in owners.values() for name in
                re.findall(r'^#print axioms\s+([\w.]+)', p.read_text(), re.M)}
    assert expected, 'Empty audit'
    for p in owners.values():
        # Ignore comments for the placeholder scan.
        text = re.sub(r'/\-.*?\-/', '', p.read_text(), flags=re.S)
        text = re.sub(r'--[^\n]*', '', text)
        assert not re.search(r'\b(sorry|admit)\b|^\s*axiom\s', text, re.M), p
    run = subprocess.run([sys.executable, 'tools/infra/run_locked_lake_build.py',
                          '--wait-for-build-lock', TARGET], cwd=ROOT, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / 'kernel.log').write_text(run.stdout)
    assert run.returncode == 0, 'Kernel build failed; see kernel.log'
    audited = {name: {a.strip() for a in axioms.split(',') if a.strip()}
               for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", run.stdout)}
    missing = expected - audited.keys()
    assert not missing, f'Audit output missing: {sorted(missing)}'
    assert all(audited[name] <= ALLOWED for name in expected), 'Nonstandard axiom'
    after = {str(p.relative_to(ROOT)): sha(p) for p in owners.values()}
    assert before == after, 'Concurrent source change; rerun after writers finish'
    cas = {}
    for script in ['verify_detector_cross_section_duality.py', 'verify_finite_log_transport.py',
                   'verify_detector_ensemble.py']:
        p = ROOT / 'scripts' / script
        result = subprocess.run([sys.executable, str(p)], cwd=ROOT, capture_output=True, text=True)
        assert result.returncode == 0, result.stderr
        cas[script] = {'sha256': sha(p), 'output': result.stdout}
    manifest = {'status': 'KERNEL_VERIFIED_SOURCE_SNAPSHOT', 'target': TARGET,
                'seal_script_sha256': sha(Path(__file__)),
                'theorems_audited': len(expected), 'repo_owned_imports_hashed': before,
                'axioms': sorted(set().union(*(audited[name] for name in expected))),
                'configuration': {f: sha(ROOT/f) for f in ['lean-toolchain', 'lake-manifest.json', 'lakefile.lean']},
                'kernel_log_sha256': sha(OUT/'kernel.log'), 'cas': cas,
                'qualifications': ['Source-hashed mathematical contracts, not experimental validation.',
                                   'Existing dependency/local-source warnings are retained in kernel.log.',
                                   'Modified external dependency contents are not certified by manifest hashes.']}
    (OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k: manifest[k] for k in ['status','target','theorems_audited','axioms']}, indent=2))


if __name__ == '__main__':
    main()
