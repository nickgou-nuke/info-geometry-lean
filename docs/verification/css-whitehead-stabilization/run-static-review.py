from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path('/workspace/scratch/d18a558d1d7d/css-rigidity-lean')
OUT = Path('/workspace/scratch/d18a558d1d7d/css-qa-candidates')
NATIVE = Path('/workspace/scratch/d18a558d1d7d/css-rigidity-qa')
MATHLIB = Path('/workspace/scratch/66380c6bf432/info-geometry-lean/.lake/packages/mathlib')
BASE = 'a392af178af1fe2bcba2ba39eb405700c6ee103c'
CHECKPOINT = 'abd22cd4badf6df017cc85fa137cb2160f48eca9'
sys.path.insert(0, str(ROOT))
from tools.build_lock import BuildLock, DEFAULT_BUILD_LOCK_PATH

modules = [
    'InfoGeometry.Algebra.ElementaryMatrixOperators',
    'InfoGeometry.Algebra.WhiteheadStabilization',
    'InfoGeometry.Algebra.StablePresentationEquivalence',
    'InfoGeometry.Algebra.StablePaddingEquivalence',
    'InfoGeometry.Algebra.HyperbolicPresentationTransport',
    'InfoGeometry.Canonical.SpinorialCore.KreinAdjoint',
]
files = ['lean/' + m.replace('.', '/') + '.lean' for m in modules]
records = []

def run(command, cwd=ROOT):
    result = subprocess.run(command, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            pass_fds=(lock.fileno(),))
    record = {'command': command, 'cwd': str(cwd), 'returncode': result.returncode,
              'output': result.stdout}
    records.append(record)
    return record

def sha(data):
    return hashlib.sha256(data).hexdigest()

with BuildLock(DEFAULT_BUILD_LOCK_PATH, 'css-independent-static-review') as lock:
    native = json.loads((NATIVE / 'report.json').read_text())
    assert native['status'] == 'passed', native
    assert native['audit_required']
    assert native['targets'] == modules
    assert all(m['returncode'] == 0 and m['warnings'] == 0 and not m['reused']
               for m in native['modules']), native['modules']
    assert run(['git', 'rev-parse', 'HEAD'])['output'].strip() == CHECKPOINT
    assert run(['git', 'status', '--porcelain'])['output'] == ''
    source_hashes = {}
    theorem_counts = {}
    banned = []
    for module, path in zip(modules, files):
        data = (ROOT / path).read_bytes()
        source_hashes[module] = sha(data)
        assert source_hashes[module] == native['source_sha256'][module]
        source = data.decode()
        theorem_counts[module] = len(re.findall(r'(?m)^(?:theorem|lemma)\s+', source))
        for number, line in enumerate(source.splitlines(), 1):
            if re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', line):
                banned.append({'path': path, 'line': number, 'text': line})
        report = OUT / (module + '.placeholder.json')
        result = run(['python3', 'tools/quality/placeholder_audit.py',
                      '--root', path, '--strict', '--json-out', str(report)])
        print(module, 'placeholder exit', result['returncode'], flush=True)
    semantic = run(['python3', 'tools/quality/semantic_vacuity_gate.py', *files,
                    '--fail-on', 'warning', '--json-out', str(OUT / 'semantic.json')])
    print('semantic warning threshold exit', semantic['returncode'], flush=True)
    comparisons = {}
    for path in [files[-1], 'lean-toolchain', 'lake-manifest.json']:
        base = run(['git', 'show', BASE + ':' + path])
        assert base['returncode'] == 0
        data = (ROOT / path).read_bytes()
        comparisons[path] = {'same_as_base': data == base['output'].encode(),
                             'sha256': sha(data)}
        assert comparisons[path]['same_as_base']
    dependency_status = []
    manifest = json.loads((MATHLIB / 'lake-manifest.json').read_text())
    dependency_pins = {p['name']: p.get('rev') for p in manifest['packages']}
    dependency_pins['mathlib'] = native['mathlib']
    for repo in [MATHLIB, *sorted((MATHLIB / '.lake/packages').iterdir())]:
        if not (repo / '.git').exists():
            continue
        status = run(['git', 'status', '--short'], repo)
        head = run(['git', 'rev-parse', 'HEAD'], repo)
        expected = dependency_pins.get(repo.name)
        dependency_status.append({'path': str(repo), 'status': status['output'],
                                  'returncode': status['returncode'],
                                  'head': head['output'].strip(), 'expected': expected,
                                  'revision_matches': expected == head['output'].strip()})
    summary = {'checkpoint': CHECKPOINT, 'base': BASE,
               'native_output': str(NATIVE), 'source_sha256': source_hashes,
               'named_theorem_counts': theorem_counts, 'banned_token_findings': banned,
               'base_comparisons': comparisons, 'dependency_status': dependency_status,
               'records': records}
    assert not banned, banned
    assert run(['git', 'status', '--porcelain'])['output'] == ''
    (OUT / 'static-gates.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('Static record saved; findings require manual disposition.', flush=True)
