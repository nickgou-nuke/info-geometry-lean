#!/usr/bin/env python3
"""Check the complete project import closure against the pinned mathlib."""
import fcntl
import json
import os
from pathlib import Path
import re
import subprocess
import sys

repo = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(repo))
from tools.quality.check_reviewed_prs import closure

sources = [
    'InfoGeometry.OperatorAlgebra.SymmetricDissipator',
    'InfoGeometry.Canonical.SymmetricDissipatorColimit',
    'InfoGeometry.Canonical.SymmetricDissipatorParity',
]
audit = 'InfoGeometry.Canonical.SymmetricDissipatorAudit'
ordered, _, native = closure(repo, [audit])
logs = repo / '.artifacts/chiral-dissipator-colimit'
logs.mkdir(parents=True, exist_ok=True)
temp = Path(os.environ['RUNNER_TEMP'])
mathlib = temp / 'chiral-dissipator-mathlib'
out = temp / 'chiral-dissipator-oleans'
env = os.environ.copy()

def run(cmd, cwd=repo):
    return subprocess.check_output(cmd, cwd=cwd, env=env, text=True)

with open('/tmp/info-geometry-build.lock', 'a+') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    processes = run(['ps', '-eo', 'stat=,comm='])
    if any(p.split()[-1] in {'lean', 'lake', 'leanc'} and
           not p.split()[0].startswith('Z') for p in processes.splitlines()):
        raise RuntimeError('Another compiler is active')
    manifest = json.loads((repo / 'lake-manifest.json').read_text())
    pin = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
    if not (mathlib / '.git').exists():
        run(['git', 'init', str(mathlib)])
        run(['git', 'remote', 'add', 'origin', 'https://github.com/leanprover-community/mathlib4.git'], mathlib)
        run(['git', 'fetch', '--depth', '1', 'origin', pin], mathlib)
        run(['git', 'checkout', '--detach', 'FETCH_HEAD'], mathlib)
    assert run(['git', 'rev-parse', 'HEAD'], mathlib).strip() == pin
    assert (repo / 'lean-toolchain').read_bytes() == (mathlib / 'lean-toolchain').read_bytes()
    print(run(['lean', '--version']), run(['lake', '--version']), pin, flush=True)
    print(run(['git', 'rev-parse', 'HEAD']), flush=True)
    print(run(['lake', 'exe', 'cache', 'get', *sorted(native)], mathlib), flush=True)
    lp = run(['lake', 'env', 'printenv', 'LEAN_PATH'], mathlib).strip()
    paths = [str((mathlib / p).resolve()) if not Path(p).is_absolute() else p
             for p in lp.split(os.pathsep) if p]
    env['LEAN_PATH'] = os.pathsep.join([str(out), *paths])
    for module in ordered:
        rel = Path(module.replace('.', '/') + '.lean')
        target = (out / rel).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        cmd = ['lean', '--root=' + str(repo / 'lean')]
        if module in sources or module == audit:
            cmd += ['-DwarningAsError=true']
        cmd += ['-o', str(target), str(repo / 'lean' / rel)]
        result = subprocess.run(cmd, cwd=repo, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (logs / (module + '.log')).write_text(result.stdout)
        print('CHECK', module, result.returncode, flush=True)
        print(result.stdout, flush=True)
        if result.returncode:
            sys.exit(result.returncode)

expected = set()
for module in sources:
    source = repo / 'lean' / (module.replace('.', '/') + '.lean')
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', text)
    ns = re.search(r'^namespace (\S+)', text, re.M)[1]
    expected.update(ns + '.' + n for n in re.findall(r'^(?:def|theorem) (\w+)', text, re.M))
text = (logs / (audit + '.log')).read_text()
reports = {n: {a.strip() for a in deps.split(',') if a.strip()}
           for n, deps in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text)}
reports.update({n: set() for n in re.findall(r"'([^']+)' does not depend on any axioms", text)})
assert set(reports) == expected, (set(reports) ^ expected)
assert all(a <= {'propext', 'Classical.choice', 'Quot.sound'} for a in reports.values())
print('AXIOM_AUDIT_PASS', len(reports), 'declarations;', len(ordered), 'modules')
subprocess.run([sys.executable, str(repo / 'tools/quality/semantic_vacuity_gate.py'),
                *[str(repo / 'lean' / (m.replace('.', '/') + '.lean')) for m in sources],
                '--fail-on', 'error', '--json-out', str(logs / 'vacuity.json')],
               cwd=repo, check=True)
