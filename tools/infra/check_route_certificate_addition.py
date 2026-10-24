"""Sequential CI check for the route-certificate addition; pins remain unchanged."""
from __future__ import annotations

import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


def main() -> None:
    repo = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(repo))
    lock = open('/tmp/info-geometry-build.lock', 'a')
    fcntl.flock(lock, fcntl.LOCK_EX)
    active = subprocess.check_output(['ps', '-eo', 'pid,comm'], text=True)
    if any(s.split()[-1] in {'lean', 'lake', 'pytest'} for s in active.splitlines() if s.split()):
        raise RuntimeError('Another build or test process is active')
    temp = Path(os.environ['RUNNER_TEMP'])
    work, out = temp / 'route-certificate-mathlib', temp / 'route-certificate-deliverable'
    out.mkdir()
    log: list[str] = []

    def run(*args: str, cwd: Path = repo, record: bool = False) -> str:
        result = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
        text = result.stdout + result.stderr
        if record or result.returncode:
            log.append(text)
            (out / 'compile.txt').write_text('\n'.join(log))
            print(text, flush=True)
        result.check_returncode()
        return text

    runtime_log = []
    for pattern in ('test_functional_route_fibers.py', 'test_route_diagnostics_torch.py',
                    'test_route_certificate.py'):
        runtime_log.append(run(sys.executable, '-m', 'unittest', 'discover', '-s', 'tests',
                               '-p', pattern, '-v', record=True))
    (out / 'python_tests.txt').write_text('\n'.join(runtime_log))
    pin = next(p for p in json.loads((repo / 'lake-manifest.json').read_text())['packages']
               if p['name'] == 'mathlib')
    run('git', 'init', str(work))
    run('git', '-C', str(work), 'remote', 'add', 'origin', pin['url'])
    run('git', '-C', str(work), 'fetch', '--depth=1', 'origin', pin['rev'])
    run('git', '-C', str(work), 'checkout', '--detach', 'FETCH_HEAD')
    assert (work / 'lean-toolchain').read_text().strip() == (repo / 'lean-toolchain').read_text().strip()
    run('lake', 'exe', 'cache', 'get', cwd=work)
    target = 'InfoGeometry.Routing.FunctionalRouteCertificate'
    seen, order = set(), []

    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        rel = Path(*module.split('.')).with_suffix('.lean')
        source = repo / 'lean' / rel
        if not source.is_file():
            raise RuntimeError(f'Missing owner: {module}')
        for dep in re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)', source.read_text(), re.M):
            if not dep.startswith(('Mathlib', 'Lean', 'Std', 'Init', 'Batteries')):
                visit(dep)
        order.append((module, rel, source))

    visit(target)
    heads = []
    for module, rel, source in order:
        text = source.read_text()
        if module == target:
            if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', text):
                raise RuntimeError('Forbidden proof construct in addition')
            heads = [module + '.' + name for name in re.findall(r'^theorem\s+(\w+)', text, re.M)]
        dest = work / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, dest)
        obj = work / '.lake/build/lib/lean' / rel.with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        print('CHECK', module, flush=True)
        run('lake', 'env', 'lean', '-o', str(obj), str(rel), cwd=work, record=True)

    def audit_footprints(text: str, count: int) -> None:
        footprints = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text, re.S)
        empty = re.findall(r'does not depend on any axioms', text)
        assert len(footprints) + len(empty) == count, 'Missing axiom audit'
        for footprint in footprints:
            assert {s.strip() for s in footprint.split(',') if s.strip()} <= {
                'propext', 'Classical.choice', 'Quot.sound'}, footprint

    audit = '\n'.join(['import ' + target] + ['#print axioms ' + h for h in heads]) + '\n'
    (work / 'RouteCertificateAudit.lean').write_text(audit)
    text = run('lake', 'env', 'lean', 'RouteCertificateAudit.lean', cwd=work, record=True)
    audit_footprints(text, len(heads))
    (out / 'audit.txt').write_text(text)
    (out / 'RouteCertificateAudit.lean').write_text(audit)
    from tools.route_certificate import certificate_from_route, emit_lean
    fixtures = [[0], [1, 0], [1, 2, 0], [0, 0], [0, 0, 1, 1], [0, 0, 1, 2],
                [1, 2, 0, 2, 3, 4], [1, 0, 0, 2, 5, 4, 5, 6]]
    generated_dir = out / 'generated'
    generated_dir.mkdir()
    for j, route in enumerate(fixtures):
        name = f'RouteFixture{j}'
        text = emit_lean(certificate_from_route(route), name)
        (work / (name + '.lean')).write_text(text)
        (generated_dir / (name + '.lean')).write_text(text)
        verdict = run('lake', 'env', 'lean', name + '.lean', cwd=work, record=True)
        audit_footprints(verdict, 3)
        (generated_dir / (name + '.audit.txt')).write_text(verdict)
    # Deliberately forge the data AFTER the independent Python checks.
    bad = emit_lean(certificate_from_route([0, 0, 1, 1]), 'ForgedRoute')
    original = 'def depth : Fin 4 → ℕ := ![0, 1, 2, 2]'
    assert original in bad
    bad = bad.replace(original, 'def depth : Fin 4 → ℕ := ![0, 0, 0, 0]')
    (work / 'ForgedRoute.lean').write_text(bad)
    rejected = subprocess.run(['lake', 'env', 'lean', 'ForgedRoute.lean'], cwd=work,
                              capture_output=True, text=True)
    (out / 'forged_certificate_rejection.txt').write_text(rejected.stdout + rejected.stderr)
    assert rejected.returncode != 0 and 'local_certificate' in rejected.stdout + rejected.stderr, \
        'A forged certificate was not rejected at its local proof'
    paths = [Path('lean') / Path(*target.split('.')).with_suffix('.lean'),
             Path('tools/route_certificate.py'), Path('tests/test_route_certificate.py'),
             Path('tools/infra/check_route_certificate_addition.py'),
             Path('.github/workflows/route-certificate.yml'), Path('docs/ROUTE_CERTIFICATE_ADDITION.md')]
    hashes = {}
    for rel in paths:
        dest = out / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(repo / rel, dest)
        hashes[str(rel)] = hashlib.sha256(dest.read_bytes()).hexdigest()
    import torch
    status = {'result': 'success', 'source_commit': run('git', 'rev-parse', 'HEAD').strip(),
              'mathlib_commit': pin['rev'], 'toolchain': (repo / 'lean-toolchain').read_text().strip(),
              'declarations': heads, 'compiled_modules': [m for m, _, _ in order],
              'generated_certificate_count': len(fixtures), 'generated_theorem_audits': 3 * len(fixtures),
              'forged_certificate_rejected': True, 'runtime_test_count': 19,
              'torch': torch.__version__, 'sha256': hashes,
              'workflow_run': os.environ['GITHUB_RUN_ID'],
              'scope': 'local certificate theorem, full source closure, eight generated certificates and runtime tests'}
    (out / 'status.json').write_text(json.dumps(status, indent=2))
    print(json.dumps(status, indent=2), flush=True)


if __name__ == '__main__':
    main()
