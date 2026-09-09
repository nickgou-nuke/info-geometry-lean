#!/usr/bin/env python3
"""Independent algebra diagnostics. These are not Lean kernel certificates."""
from __future__ import annotations
from fractions import Fraction
import importlib.util
import json
from pathlib import Path
import sys
import sympy as s

ROOT = Path(__file__).resolve().parents[2]
path = ROOT / 'tools/quality/check_operator_zorn_gauge_algebra.py'
spec = importlib.util.spec_from_file_location('ordered_zorn_parent', path)
if spec is None or spec.loader is None:
    raise RuntimeError('The existing parent ordered-coefficient checker is required')
nc = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = nc
spec.loader.exec_module(nc)


def main() -> None:
    checks = []
    def exact(name, lhs, rhs, kind='free noncommuting coefficient identity'):
        if isinstance(lhs, nc.P):
            ok = lhs == rhs
        elif isinstance(lhs, s.MatrixBase):
            ok = lhs.shape == rhs.shape and all(s.simplify(v) == 0 for v in lhs-rhs)
        elif isinstance(lhs, (tuple,list)):
            if len(lhs) != len(rhs): raise AssertionError(name + ': different arity')
            ok = all(a == b if isinstance(a,nc.P) else s.simplify(a-b) == 0
                     for a,b in zip(lhs,rhs))
        else:
            ok = s.simplify(lhs-rhs) == 0
        if not ok: raise AssertionError(name)
        checks.append({'name':name, 'kind':kind, 'passed':True})
    def counterexample(name, condition):
        if not bool(condition): raise AssertionError(name)
        checks.append({'name':name, 'kind':'exact finite counterexample', 'passed':True})

    X,Y,Z = nc.symbols('x'),nc.symbols('y'),nc.symbols('z')
    p,q,r,t = [nc.P.atom(x) for x in ('p','q','r','t')]
    zero = nc.zero
    half = nc.P({():Fraction(1,2)})
    add,sub,mul = nc.za,nc.zs,nc.zm
    diag = lambda a:(a,a,zero,zero,zero,zero,zero,zero)
    exchange = lambda x:(x[1],x[0],*(-a for a in x[5:8]),*(-a for a in x[2:5]))
    unsigned = lambda x:(x[1],x[0],*x[5:8],*x[2:5])
    corner = lambda a,b,x:mul(mul(diag(a),x),diag(b))
    U,V = X[2:5],Y[2:5]
    pairs = [(1,2),(2,0),(0,1)]
    commtwice = tuple(nc.cb(U[j],V[k])-nc.cb(U[k],V[j]) for j,k in pairs)
    exact('epsilon commutator equals symmetric cross',commtwice,add(nc.cross(U,V),nc.cross(V,U)))
    ext = tuple(half*a for a in sub(nc.cross(U,V),nc.cross(V,U)))
    com = tuple(half*a for a in commtwice)
    exact('ordered cross reconstruction',add(ext,com),nc.cross(U,V))
    exact('ordered dot reconstruction',half*(nc.dot(U,V)+nc.dot(V,U))+half*(nc.dot(U,V)-nc.dot(V,U)),nc.dot(U,V))
    exact('signed exchange involution',exchange(exchange(X)),X)
    exact('signed exchange product',exchange(mul(X,Y)),mul(exchange(X),exchange(Y)))
    exact('signed exchange associator',exchange(nc.assoc(X,Y,Z)),nc.assoc(exchange(X),exchange(Y),exchange(Z)))
    upper=nc.cross(X[2:5],Y[2:5]); lower=nc.cross(X[5:8],Y[5:8])
    exact('unsigned flip product defect',sub(unsigned(mul(X,Y)),mul(unsigned(X),unsigned(Y))),
          (zero,zero,*(a+a for a in upper),*(-(a+a) for a in lower)))
    exact('coefficient embedding multiplication',mul(diag(p),diag(q)),diag(p*q))
    exact('left nucleus',mul(mul(diag(p),X),Y),mul(diag(p),mul(X,Y)))
    exact('middle nucleus',mul(mul(X,diag(p)),Y),mul(X,mul(diag(p),Y)))
    exact('right nucleus',mul(mul(X,Y),diag(p)),mul(X,mul(Y,diag(p))))
    exact('corner coordinates',corner(p,q,X),tuple(p*a*q for a in X))
    exact('corner product with ordered middle overlap',mul(corner(p,q,X),corner(r,t,Y)),
          corner(p,t,mul(X,mul(diag(q*r),Y))))
    exact('exchange corner',exchange(corner(p,q,X)),corner(p,q,exchange(X)))
    exact('exchange coefficient derivation',exchange(nc.delta(p,X)),nc.delta(p,exchange(X)))
    exact('exchange curvature action',exchange(nc.curv(p,q,X,Y,Z)),
          nc.curv(p,q,exchange(X),exchange(Y),exchange(Z)))
    exact('exchange full associator alternation',exchange(nc.alt(X,Y,Z)),
          nc.alt(exchange(X),exchange(Y),exchange(Z)))
    exact('exchange gauge',exchange(nc.gauge(X)),nc.gauge(exchange(X)))
    exact('gauge corner',nc.gauge(corner(p,q,X)),corner(nc.cg(p),nc.cg(q),nc.gauge(X)))

    # Literal proposed product on scalar coefficients: its commutator cross is zero.
    def source_product(x,y):
        a,b,u,v=x[0],x[1],x[2:5],x[5:8]
        c,d,w,t=y[0],y[1],y[2:5],y[5:8]
        return (a*c+sum(u[i]*t[i] for i in range(3)),
                b*d+sum(v[i]*w[i] for i in range(3)),
                *(a*w[i]+u[i]*d for i in range(3)),
                *(b*t[i]+v[i]*c for i in range(3)))
    sx=(0,0,1,0,0,1,0,0); sy=(0,0,0,1,0,0,0,0)
    counterexample('literal source product is not left alternative',
        source_product(source_product(sx,sx),sy)!=source_product(sx,source_product(sx,sy)))
    exact('native classical cross survives',nc.cross((1,0,0),(0,1,0)),(0,0,1),'exact scalar example')

    clock=s.diag(1,s.I,-1,-s.I)
    raising=s.zeros(4)
    for j in range(3): raising[j+1,j]=1
    projectors=[s.diag(*(int(i==k) for i in range(4))) for k in range(4)]
    kind='exact finite coefficient-matrix identity'
    exact('clock fourth power',clock**4,s.eye(4),kind)
    exact('raising fourth power',raising**4,s.zeros(4),kind)
    counterexample('raising cube is nonzero',raising**3 != s.zeros(4))
    exact('multiplicative q-commutation',clock*raising,s.I*raising*clock,kind)
    counterexample('ordinary source commutator fails',clock*raising-raising*clock != s.I*raising)
    for k,pk in enumerate(projectors):
        fourier=sum(((-s.I)**(k*m)*clock**m for m in range(4)),s.zeros(4))/4
        exact(f'Fourier projector {k}',fourier,pk,kind)
        exact(f'raising sector {k}',raising*pk,projectors[(k+1)%4]*raising,kind)
        for j,pj in enumerate(projectors):
            exact(f'projector product {j},{k}',pj*pk,pk if j==k else s.zeros(4),kind)
    exact('projector resolution',sum(projectors,s.zeros(4)),s.eye(4),kind)
    M=s.Matrix(4,4,s.symbols('a0:16'))
    exact('all sixteen coefficient blocks reconstruct',
          sum((p*M*q for p in projectors for q in projectors),s.zeros(4)),M,kind)
    exact('diagonal-only extraction loses raising',sum((p*raising*p for p in projectors),s.zeros(4)),s.zeros(4),kind)
    counterexample('lost raising field is nonzero',raising != s.zeros(4))

    psi=s.Matrix(s.symbols('psi0:2')); phi=s.Matrix(s.symbols('phi0:2'))
    Q=s.Matrix(2,2,s.symbols('q0:4'))
    Ppsi=psi*psi.conjugate().T; Pphi=phi*phi.conjugate().T
    overlap=(phi.conjugate().T*psi)[0]
    reverse=(psi.conjugate().T*phi)[0]
    numerator=(phi.conjugate().T*Q*psi)[0]
    rankkind='exact finite rank-one coefficient identity'
    exact('dyad square before normalization',Ppsi*Ppsi,(psi.conjugate().T*psi)[0]*Ppsi,rankkind)
    exact('twin trace numerator',s.trace(Pphi*Q*Ppsi),numerator*reverse,rankkind)
    exact('twin trace denominator',s.trace(Pphi*Ppsi),overlap*reverse,rankkind)
    a,b=s.symbols('a b',nonzero=True)
    exact('independent homogeneous amplitude ratio',
          s.cancel((s.conjugate(b)*a*numerator)/(s.conjugate(b)*a*overlap)),numerator/overlap,rankkind)
    orthogonal_psi=s.Matrix([1,0]); orthogonal_phi=s.Matrix([0,1])
    exact('undefined-locus overlap',(orthogonal_phi.T*orthogonal_psi)[0],0,'exact orthogonal-boundary example')
    counterexample('linear and conjugate-linear scalar laws differ',s.I != -s.I)

    report={'lean_kernel_verified':False,'status':'passed','check_count':len(checks),
            'checks':checks,'scope':'Independent exact algebraic diagnostics, not Lean elaboration.'}
    (ROOT/'reports').mkdir(exist_ok=True)
    (ROOT/'reports/operator-zorn-twin-exact.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))

if __name__=='__main__':
    main()
