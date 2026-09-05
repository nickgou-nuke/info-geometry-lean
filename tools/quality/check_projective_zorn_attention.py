#!/usr/bin/env python3
"""Independent algebra diagnostics; not Lean elaboration or kernel evidence."""
from __future__ import annotations
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import sympy as s

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('ordered_zorn', ROOT/'tools/quality/check_operator_zorn_gauge_algebra.py')
assert spec and spec.loader
nc = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = nc
spec.loader.exec_module(nc)


def main() -> None:
    checks: list[dict] = []
    def eq(name, lhs, rhs, kind='symbolic identity'):
        vals = list(lhs-rhs) if isinstance(lhs, s.MatrixBase) else [lhs-rhs]
        if not all(s.simplify(v) == 0 for v in vals):
            raise AssertionError(name)
        checks.append({'name':name, 'kind':kind, 'passed':True})
    def neq(name,lhs,rhs):
        if lhs == rhs: raise AssertionError(name)
        checks.append({'name':name,'kind':'exact counterexample','passed':True})

    w=s.symbols('w0:3',positive=True); v=s.symbols('v0:3',real=True)
    z=s.symbols('z0:3',positive=True); c,d=s.symbols('c d',positive=True); b=s.symbols('b',real=True)
    ratio=lambda a,i,j:a[i]/a[j]
    for i,j in itertools.product(range(3),repeat=2):
        eq(f'independent scale cross-ratio {i}{j}',
           ((c*w[i])*(d*z[j]))/((c*w[j])*(d*z[i])),(w[i]*z[j])/(w[j]*z[i]))
        eq(f'horizontal log differential {i}{j}',
           (c*v[i]+b*w[i])/(c*w[i])-(c*v[j]+b*w[j])/(c*w[j]),v[i]/w[i]-v[j]/w[j])
    eq('ratio cocycle',ratio(w,0,1)*ratio(w,1,2),ratio(w,0,2))
    Z=sum(w); p=[x/Z for x in w]; f=s.symbols('f0:3',real=True)
    m=sum(p[i]*f[i] for i in range(3))
    eq('centered covariance',sum(p[i]*(f[i]-m)**2 for i in range(3)),sum(p[i]*f[i]**2 for i in range(3))-m*m)
    mv=sum(v)/Z
    fisher=sum(p[i]*(v[i]/w[i]-mv)**2 for i in range(3))
    eq('Fisher homogeneous expression',fisher,sum(v[i]**2/w[i] for i in range(3))/Z-mv**2)
    eq('Fisher radial zero',fisher.subs({v[i]:b*w[i] for i in range(3)}),0)
    t=s.symbols('t',real=True)
    for i,j in [(0,1),(1,2),(2,0)]:
        eq(f'log ratio actual derivative {i}{j}',s.diff(s.log(w[i]+t*v[i])-s.log(w[j]+t*v[j]),t).subs(t,0),v[i]/w[i]-v[j]/w[j])
    beta=s.symbols('beta',real=True); scores=s.symbols('s0:3',real=True)
    W=[w[i]*s.exp(beta*scores[i]) for i in range(3)]; part=sum(W); prob=[u/part for u in W]
    mean_score=sum(prob[i]*scores[i] for i in range(3))
    eq('positive score sign',s.diff(s.log(part),beta),mean_score)
    eq('partition Hessian variance',s.diff(s.log(part),beta,2),sum(prob[i]*scores[i]**2 for i in range(3))-mean_score**2)
    eq('relative reference entropy',-sum(prob[i]*(beta*scores[i]-s.log(part)) for i in range(3)),s.log(part)-beta*mean_score)
    P0=s.diag(1,1,0,0); P1=s.diag(1,0,1,0)
    eq('source occupation overlap',P0*P1,s.diag(1,0,0,0),'exact finite witness')
    neq('source occupations not orthogonal',P0*P1,s.zeros(4))
    neq('source occupations not complete',P0+P1,s.eye(4))
    repoint=s.zeros(4)
    for i in range(4): repoint[i,3]=1
    neq('source occupation not central',P0*repoint,repoint*P0)
    keys=[s.Matrix([1,0]),s.Matrix([0,1]),s.Matrix([s.Rational(3,5),s.Rational(4,5)])]
    rho=s.eye(2)/2
    for i,k in enumerate(keys):
        eq(f'key {i} normalized',(k.T*k)[0],1,'exact finite witness')
        eq(f'key {i} uniform density readout',(k.T*rho*k)[0],s.Rational(1,2),'exact finite witness')
    eq('overcomplete readouts sum',sum((k.T*rho*k)[0] for k in keys),s.Rational(3,2),'exact counterexample value')
    neq('not softmax probability row',s.Rational(3,2),s.Integer(1))
    z2=s.zeros(2); eye=s.eye(2); e12=s.Matrix([[0,1],[0,0]]); e21=e12.T; e11=s.diag(1,0)
    X=(z2,z2,e12,e21,z2,z2,z2,z2); pole=(eye,z2,z2,z2,z2,z2,z2,z2)
    a=nc.assoc(X,X,pole)
    obs=lambda M:(2*M[0,0]+M[1,1])/3
    eq('nonzero normalized Zorn associator',obs(a[7]),s.Rational(1,3),'exact counterexample value')
    neq('expectation not multiplicative',obs(e11*e11),obs(e11)**2)
    M=s.Matrix(2,2,s.symbols('m0:4',real=True))
    eq('positive coefficient state squares',obs(M.T*M),sum(s.Rational(2 if i==0 else 1,3)*sum(M[j,i]**2 for j in range(2)) for i in range(2)))

    # This metric diagnostic is explicitly finite, unlike the native universal theorem scripts.
    logs=[(0,0,0),(1,-2,3),(2,4,1),(-3,1,2)]
    dist=lambda a,b:max(a[i]-b[i]-a[j]+b[j] for i,j in itertools.product(range(3),repeat=2))
    assert all(dist(a,c)<=dist(a,b)+dist(b,c) for a,b,c in itertools.product(logs,repeat=3))
    checks.append({'name':'metric triangle on 64 triples','kind':'finite sanity check, not a proof','passed':True})
    report={'lean_kernel_verified':False,'status':'passed','check_count':len(checks),'checks':checks}
    (ROOT/'reports').mkdir(exist_ok=True)
    (ROOT/'reports/projective-zorn-attention-algebra-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='checks'}))

if __name__=='__main__':
    main()
