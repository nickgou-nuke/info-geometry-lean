"""Pinned sequential source compilation and axiom audit of the pruning/Gramian/log-coupling additions."""
from __future__ import annotations
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

TARGETS = [
    'InfoGeometry.Routing.CaratheodoryPivotContracts',
    'InfoGeometry.Canonical.GramianInverseContracts',
    'InfoGeometry.Canonical.FiniteSteinInverse',
    'InfoGeometry.Probability.BipartiteLogCoupling',
    'InfoGeometry.Routing.ShapeSinkhornBipartite',
]


def lean_code(text: str) -> str:
    """Remove nested block and line comments, retaining line positions."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                out.extend('  ')
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
            else:
                if text[i] == '"':
                    quoted = False
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.extend('  ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end - i))
            i = end
        else:
            if text[i] == '"':
                quoted = True
            out.append(text[i])
            i += 1
    return ''.join(out)


def main() -> None:
    repo = Path.cwd()
    lock = open('/tmp/info-geometry-build.lock', 'a', encoding='utf-8')
    fcntl.flock(lock, fcntl.LOCK_EX)
    processes = subprocess.check_output(['ps', '-eo', 'pid,comm'], text=True)
    if any(line.split()[-1] in {'lean', 'lake', 'pytest'}
           for line in processes.splitlines() if line.split()):
        raise RuntimeError('Another compiler or test process is active')
    tmp = Path(os.environ.get('RUNNER_TEMP', tempfile.gettempdir()))
    work = Path(tempfile.mkdtemp(prefix='pruning-gramian-coupling-mathlib-', dir=tmp))
    out = tmp / 'pruning-gramian-coupling-deliverable'
    out.mkdir(exist_ok=True)
    logs = []

    def run(*args: str, cwd: Path = repo, verbose: bool = False) -> str:
        result = subprocess.run(args, cwd=cwd, text=True, capture_output=True)
        if verbose or result.returncode:
            text = result.stdout + result.stderr
            logs.append(text)
            (out / 'compile.txt').write_text('\n'.join(logs), encoding='utf-8')
            print(text, flush=True)
        result.check_returncode()
        return result.stdout

    manifest = json.loads((repo / 'lake-manifest.json').read_text())
    pins = {p['name']: p for p in manifest['packages']}
    pin = pins['mathlib']
    print('MATHLIB_PIN', pin['rev'], flush=True)
    run('git', 'init', str(work))
    run('git', '-C', str(work), 'remote', 'add', 'origin', pin['url'])
    run('git', '-C', str(work), 'fetch', '--depth=1', 'origin', pin['rev'])
    run('git', '-C', str(work), 'checkout', '--detach', 'FETCH_HEAD')
    toolchain = (repo / 'lean-toolchain').read_text().strip()
    if (work / 'lean-toolchain').read_text().strip() != toolchain:
        raise RuntimeError('Toolchain mismatch')
    run('lake', 'exe', 'cache', 'get', cwd=work)
    external, external_pins = {}, {}
    roots = [work / '.lake/build/lib/lean'] + list(
        (work / '.lake/packages').glob('*/.lake/build/lib/lean'))
    package_names = {'Architect': 'LeanArchitect', 'Cli': 'Cli',
                     'LeanCopilot': 'LeanCopilot'}
    seen, active, order = set(), [], []
    names, hashes = [], {}
    for module in TARGETS:
        relative = Path('lean', *module.split('.')).with_suffix('.lean')
        source = repo / relative
        destination = out / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        hashes[str(relative)] = hashlib.sha256(source.read_bytes()).hexdigest()

    def visit(module: str) -> None:
        if module in active:
            raise RuntimeError('Import cycle: ' + ' -> '.join(active + [module]))
        if module in seen:
            return
        root = module.split('.')[0]
        relative = Path(*module.split('.')).with_suffix('.lean')
        if root in {'Mathlib', 'Lean', 'Std', 'Init', 'Lake'}:
            return
        source = repo / 'lean' / relative
        if not source.is_file():
            if any((r / relative.with_suffix('.olean')).is_file() for r in roots):
                return
            package = package_names.get(root, root)
            if package not in pins:
                raise RuntimeError('Missing pinned owner: ' + ' -> '.join(active + [module]))
            if package not in external:
                p = pins[package]
                if p['type'] == 'path':
                    external[package] = repo / p['dir']
                else:
                    checkout = Path(tempfile.mkdtemp(prefix=f'car-{package}-', dir=tmp))
                    run('git', 'init', str(checkout))
                    run('git', '-C', str(checkout), 'remote', 'add', 'origin', p['url'])
                    run('git', '-C', str(checkout), 'fetch', '--depth=1', 'origin', p['rev'])
                    run('git', '-C', str(checkout), 'checkout', '--detach', 'FETCH_HEAD')
                    external[package] = checkout / (p.get('subDir') or '')
                    external_pins[package] = p['rev']
            source = external[package] / relative
            if not source.is_file():
                raise RuntimeError(f'Missing exact external source: {source}')
        active.append(module)
        for dep in re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)',
                              lean_code(source.read_text()), re.M):
            visit(dep)
        active.pop()
        seen.add(module)
        order.append((module, relative, source))

    for target in TARGETS:
        visit(target)
    closure = {'modules': [m for m, _, _ in order], 'external_pins': external_pins}
    (out / 'closure.json').write_text(json.dumps(closure, indent=2))
    print('OWNER_CLOSURE', closure, flush=True)
    for module, relative, source in order:
        text = source.read_text()
        if module in TARGETS:
            if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', lean_code(text)):
                raise RuntimeError(f'Forbidden proof construct: {module}')
            heads = re.findall(r'^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma|def)\s+(\w+)', text, re.M)
            names.extend(f'{module}.{name}' for name in heads)
        destination = work / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        olean = work / '.lake/build/lib/lean' / relative.with_suffix('.olean')
        olean.parent.mkdir(parents=True, exist_ok=True)
        print('CHECK', module, flush=True)
        run('lake', 'env', 'lean', '-o', str(olean), str(relative), cwd=work, verbose=True)
    audit = '\n'.join([f'import {m}' for m in TARGETS] +
                      [f'#print axioms {name}' for name in names]) + '\n'
    (work / 'PruningGramianCouplingAudit.lean').write_text(audit, encoding='utf-8')
    (out / 'PruningGramianCouplingAudit.lean').write_text(audit, encoding='utf-8')
    audit_text = run('lake', 'env', 'lean', 'PruningGramianCouplingAudit.lean', cwd=work, verbose=True)
    footprints = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', audit_text, re.S)
    empty = re.findall('does not depend on any axioms', audit_text)
    if len(footprints) + len(empty) != len(names):
        raise RuntimeError('Missing declaration audits')
    for footprint in footprints:
        if not {x.strip() for x in footprint.split(',') if x.strip()} <= {
                'propext', 'Classical.choice', 'Quot.sound'}:
            raise RuntimeError(f'Unexpected axioms: {footprint}')
    (out / 'audit.txt').write_text(audit_text, encoding='utf-8')
    for relative in ['docs/PRUNING_SHAPE_SINKHORN_PR.md',
                     'tools/infra/check_pruning_gramian_coupling.py',
                     '.github/workflows/pruning-shape-sinkhorn.yml']:
        destination = out / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(repo / relative, destination)
        hashes[relative] = hashlib.sha256((repo / relative).read_bytes()).hexdigest()
    status = {'result': 'success', 'source_commit': run('git', 'rev-parse', 'HEAD').strip(),
              'lean_toolchain': toolchain, 'mathlib_commit': pin['rev'],
              'compiled_modules': [m for m, _, _ in order], 'external_pins': external_pins,
              'audited_declarations': names, 'source_sha256': hashes,
              'workflow_run': os.environ.get('GITHUB_RUN_ID'),
              'scope': 'new modules and exact source import closure, not full repository'}
    (out / 'status.json').write_text(json.dumps(status, indent=2), encoding='utf-8')
    print('AUDITED_DECLARATIONS', len(names), flush=True)


if __name__ == '__main__':
    main()
