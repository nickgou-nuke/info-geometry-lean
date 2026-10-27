#!/usr/bin/env python3
"""Compile exact sources serially; audit all new declarations only on total success."""
from __future__ import annotations
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.quality.check_peirce_reflection import audit_source, run
from tools.quality.check_reviewed_prs import closure
TARGETS = [
    'InfoGeometry.Twistor.PerjesConventions',
    'InfoGeometry.Twistor.TwistorKinematicTensor',
    'InfoGeometry.Twistor.TwistorConstituentKinematics',
    'InfoGeometry.Twistor.TwistorInternalSymmetry',
    'InfoGeometry.Twistor.TwistorConstituentCCR',
]

def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--mathlib-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    mathlib, out = args.mathlib_root.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    state = {'status': 'pending', 'scope': 'exact-source closure, not root Lake build',
             'targets': TARGETS, 'modules': [], 'axiom_audit_passed': False}
    try:
        manifest = json.loads((ROOT/'lake-manifest.json').read_text())
        pin = next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib')
        toolchain = (ROOT/'lean-toolchain').read_text().strip()
        state.update(revision=run(['git','rev-parse','HEAD'],ROOT).strip(),
                     mathlib=pin, toolchain=toolchain)
        if run(['git','rev-parse','HEAD'],mathlib).strip()!=pin:
            raise RuntimeError('Mathlib revision mismatch')
        if (mathlib/'lean-toolchain').read_text().strip()!=toolchain:
            raise RuntimeError('Toolchain mismatch')
        ordered, dependencies, _ = closure(ROOT,TARGETS)
        src, lib = out/'src', out/'lib'
        src.mkdir(); lib.mkdir()
        (src/'lean-toolchain').write_text(toolchain+'\n')
        state['source_sha256']={}
        for module in ordered:
            rel=Path(module.replace('.','/')+'.lean')
            data=(ROOT/'lean'/rel).read_bytes()
            dest=src/rel
            dest.parent.mkdir(parents=True,exist_ok=True)
            dest.write_bytes(data)
            state['source_sha256'][module]=hashlib.sha256(data).hexdigest()
        with open('/tmp/info-geometry-build.lock','a') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX)
            if any(p.strip() in {'lean','lake','leanc'} for p in run(['ps','-eo','comm='],ROOT).splitlines()):
                raise RuntimeError('Concurrent compiler detected')
            (out/'cache.log').write_text(run(['lake','exe','cache','get'],mathlib))
            env=os.environ.copy()
            path=run(['lake','env','printenv','LEAN_PATH'],mathlib).strip()
            search=[str((mathlib/p).resolve()) if not Path(p).is_absolute() else p
                    for p in path.split(os.pathsep) if p]
            env['LEAN_PATH']=os.pathsep.join([str(lib),*search])
            (out/'lean-version.txt').write_text(run(['lean','--version'],src,env))
            failed=set()
            for module in ordered:
                blocked=[d for d in dependencies[module] if d in failed]
                if blocked:
                    failed.add(module)
                    state['modules'].append({'module':module,'status':'blocked','dependencies':blocked})
                    print('BLOCKED',module,blocked,flush=True)
                    continue
                rel=Path(module.replace('.','/'))
                olean=(lib/rel).with_suffix('.olean')
                olean.parent.mkdir(parents=True,exist_ok=True)
                result=subprocess.run(['lean','-o',str(olean),str((src/rel).with_suffix('.lean'))],
                    cwd=src,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
                (out/(module+'.log')).write_text(result.stdout)
                state['modules'].append({'module':module,'returncode':result.returncode})
                print('CHECK',module,result.returncode,flush=True)
                print(result.stdout,flush=True)
                if result.returncode: failed.add(module)
            if failed:
                state['failed_modules']=sorted(failed)
                raise RuntimeError('Compilation failed; no declaration audit performed')
            audit=src/'PerjesKleinKernelAudit.lean'
            audit.write_text(audit_source(TARGETS))
            evidence=run(['lean',str(audit)],src,env)
            (out/'audit.log').write_text(evidence)
            if 'AUDIT_COUNT:' not in evidence: raise RuntimeError('Audit incomplete')
            state.update(status='passed',axiom_audit_passed=True)
            print(evidence,flush=True)
    except Exception as error:
        state.update(status='failed',error=str(error))
        raise
    finally:
        (out/'status.json').write_text(json.dumps(state,indent=2)+'\n')

if __name__=='__main__': main()
