"""Exact-pin sequential checking of the two prefix-locality additions."""
from pathlib import Path
import fcntl
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.infra.check_pruning_gramian_coupling import lean_code

TARGETS = ['InfoGeometry.Routing.CausalPrefixPooling',
           'InfoGeometry.Routing.BlockCausalSinkhorn']


def main():
    repo = Path.cwd()
    tmp = Path(os.environ.get('RUNNER_TEMP', tempfile.gettempdir()))
    out = tmp / 'causal-sinkhorn-evidence'
    out.mkdir(exist_ok=True)
    lock = open('/tmp/info-geometry-build.lock', 'a')
    fcntl.flock(lock, fcntl.LOCK_EX)
    processes = subprocess.check_output(['ps', '-eo', 'pid,comm'], text=True)
    if any(s.split()[-1] in {'lean', 'lake'} for s in processes.splitlines() if s.split()):
        raise RuntimeError('A compiler is already active')
    logs, names, hashes = [], [], {}
    status = {'result': 'failure', 'scope': 'two new modules against unchanged pinned Mathlib; not parent or full repository'}
    def run(*args, cwd=repo):
        p = subprocess.run(args, cwd=cwd, text=True, capture_output=True)
        logs.append('$ ' + ' '.join(args) + '\n' + p.stdout + p.stderr)
        (out/'compile.txt').write_text('\n'.join(logs))
        print(p.stdout + p.stderr, flush=True)
        p.check_returncode()
        return p.stdout
    try:
        status['source_commit'] = run('git', 'rev-parse', 'HEAD').strip()
        manifest = json.loads((repo/'lake-manifest.json').read_text())
        pin = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
        work = Path(tempfile.mkdtemp(prefix='causal-sinkhorn-mathlib-', dir=tmp))
        run('git','init',str(work))
        run('git','-C',str(work),'remote','add','origin',pin['url'])
        run('git','-C',str(work),'fetch','--depth=1','origin',pin['rev'])
        run('git','-C',str(work),'checkout','--detach','FETCH_HEAD')
        toolchain=(repo/'lean-toolchain').read_text().strip()
        if (work/'lean-toolchain').read_text().strip() != toolchain:
            raise RuntimeError('Exact toolchain mismatch')
        status.update(lean_toolchain=toolchain, mathlib_commit=pin['rev'])
        run('lake','exe','cache','get',cwd=work)
        for module in TARGETS:
            rel=Path(*module.split('.')).with_suffix('.lean')
            source=repo/'lean'/rel
            text=source.read_text(); code=lean_code(text)
            if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',code):
                raise RuntimeError('Forbidden declaration/proof construct')
            imports=re.findall(r'^\s*import\s+([\w.]+)',code,re.M)
            if any(i != 'Mathlib' and i not in TARGETS for i in imports):
                raise RuntimeError('Uninspected import closure')
            for name in re.findall(r'^(?:theorem|lemma|def|abbrev)\s+(\w+)',code,re.M):
                names.append(module+'.'+name)
            dest=work/rel; dest.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(source,dest)
            evidence=out/'lean'/rel; evidence.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(source,evidence)
            hashes[str(Path('lean')/rel)]=hashlib.sha256(source.read_bytes()).hexdigest()
            olean=work/'.lake/build/lib/lean'/rel.with_suffix('.olean'); olean.parent.mkdir(parents=True,exist_ok=True)
            run('lake','env','lean','-o',str(olean),str(rel),cwd=work)
        audit='\n'.join(['import '+m for m in TARGETS]+['#print axioms '+n for n in names])+'\n'
        (work/'CausalAudit.lean').write_text(audit); (out/'CausalAudit.lean').write_text(audit)
        text=run('lake','env','lean','CausalAudit.lean',cwd=work)
        footprints=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text,re.S)
        empty=re.findall('does not depend on any axioms',text)
        if not names or len(footprints)+len(empty) != len(names):
            raise RuntimeError('Incomplete axiom audit')
        for fp in footprints:
            if not set(filter(None,(n.strip() for n in fp.split(',')))) <= {'propext','Classical.choice','Quot.sound'}:
                raise RuntimeError('Unexpected axiom footprint: '+fp)
        (out/'audit.txt').write_text(text)
        status.update(result='success',compiled_modules=TARGETS,audited_declarations=names,source_sha256=hashes)
    finally:
        (out/'status.json').write_text(json.dumps(status,indent=2)+'\n')

if __name__ == '__main__':
    main()
