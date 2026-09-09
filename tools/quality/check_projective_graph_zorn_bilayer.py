#!/usr/bin/env python3
"""Exact independent diagnostics, not Lean elaboration or kernel verification.

The parent NC-Zorn checker supplies an ordered coefficient-word algebra. Zorn
products are never reassociated. Graph tests are labelled finite examples;
they do not replace the universal native orthogonal-projection proofs.
"""
from __future__ import annotations
import importlib.util
import json
from pathlib import Path
import sys
import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    'parent_ordered_zorn', ROOT / 'tools/quality/check_operator_zorn_gauge_algebra.py')
if SPEC is None or SPEC.loader is None:
    raise RuntimeError('The existing parent NC-Zorn checker is required.')
nc = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = nc
SPEC.loader.exec_module(nc)


def main() -> None:
    checks: list[dict[str, object]] = []

    def equal(name: str, lhs, rhs, kind: str = 'exact symbolic identity') -> None:
        if isinstance(lhs, nc.P):
            ok = lhs == rhs
        elif isinstance(lhs, sp.MatrixBase):
            ok = lhs.shape == rhs.shape and all(sp.simplify(x) == 0 for x in lhs-rhs)
        elif isinstance(lhs, (tuple, list)):
            if len(lhs) != len(rhs):
                raise AssertionError(f'{name}: unequal arity')
            ok = all(x == y if isinstance(x, nc.P) else sp.simplify(x-y) == 0
                     for x, y in zip(lhs, rhs))
        else:
            ok = sp.simplify(lhs-rhs) == 0
        if not ok:
            raise AssertionError(name)
        checks.append({'name': name, 'kind': kind, 'passed': True})

    def true(name: str, condition: bool, kind: str) -> None:
        if not bool(condition):
            raise AssertionError(name)
        checks.append({'name': name, 'kind': kind, 'passed': True})

    graphs = [
        ('triangle', 3, [(0,1),(1,2),(2,0)]),
        ('path', 4, [(0,1),(1,2),(2,3)]),
        ('disconnected', 5, [(0,1),(1,2),(2,0),(3,4)]),
        ('parallel_edges', 2, [(0,1),(0,1),(1,0)]),
        ('self_loop', 2, [(0,0),(0,1)]),
        ('no_edges', 2, []),
    ]
    for name, nv, edges in graphs:
        ne = len(edges)
        B = sp.zeros(ne,nv)
        for e, (u,v) in enumerate(edges):
            B[e,u] -= 1
            B[e,v] += 1
        P = B * B.pinv() if ne else sp.zeros(0,0)
        C = sp.eye(ne)-P
        a = sp.Matrix(ne,1,sp.symbols(f'{name}_a0:{ne}'))
        phi = sp.Matrix(nv,1,sp.symbols(f'{name}_p0:{nv}'))
        j = sp.Matrix(ne,1,sp.symbols(f'{name}_j0:{ne}'))
        kind = 'exact finite graph example'
        equal(f'{name}: orthogonal projection symmetric',P.T,P,kind)
        equal(f'{name}: projection idempotent',P*P,P,kind)
        equal(f'{name}: reconstruction',P*a+C*a,a,kind)
        equal(f'{name}: cycle residual has zero incidence',B.T*C,sp.zeros(nv,ne),kind)
        equal(f'{name}: exact range fixed',P*B,B,kind)
        equal(f'{name}: owner incidence sign',(B*phi).T*j,-phi.T*(-B.T*j),kind)
        for k, cycle in enumerate(B.T.nullspace()):
            equal(f'{name}: cycle {k} annihilates gradient',cycle.T*B,sp.zeros(1,nv),kind)
            equal(f'{name}: cycle {k} production splitting',cycle.T*a,cycle.T*C*a,kind)

    # State normalization and kinetic normalization are distinct.
    w0,w1,c = sp.symbols('w0 w1 c',positive=True)
    k,l = sp.symbols('k l',positive=True)
    p0,p1 = w0/(w0+w1),w1/(w0+w1)
    x,y = p0*k,p1*l
    equal('homogeneous probabilities cancel state scale',c*w0/(c*w0+c*w1),p0)
    equal('flux log-affinity split',sp.expand_log(sp.log(x/y),force=True),
          sp.expand_log(sp.log(k/l)-(sp.log(p1)-sp.log(p0)),force=True))
    sigma = (x-y)*sp.log(x/y)
    sigmac = (c*x-c*y)*sp.log((c*x)/(c*y))
    equal('production changes with kinetic scale',sigmac,c*sigma)
    equal('traffic changes with kinetic scale',c*x+c*y,c*(x+y))
    equal('production per traffic is kinetic-scale invariant',sigmac/(c*x+c*y),sigma/(x+y))
    # Three equal forward biases with a genuinely steady normalized current.
    flux_plus = sp.Rational(2,3)
    flux_minus = sp.Rational(1,3)
    equal('steady biased triangle entropy',3*(flux_plus-flux_minus)*sp.log(flux_plus/flux_minus),sp.log(2),'exact finite kinetic example')
    equal('steady biased triangle traffic',3*(flux_plus+flux_minus),3,'exact finite kinetic example')
    equal('steady biased triangle relative production',3*(flux_plus-flux_minus)*sp.log(flux_plus/flux_minus)/(3*(flux_plus+flux_minus)),sp.log(2)/3,'exact finite kinetic example')
    # An arbitrary rate-affinity pairing need not be positive away from stationarity.
    xp,yp = sp.Rational(2,100),sp.Rational(99,100)
    true('nonsteady rate affinity pairing can be negative',xp-yp < 0 and 2 > 1,
         'exact sign counterexample with log(2)>0')
    true('the same nonsteady flux affinity has positive production',xp-yp < 0 and 0 < xp/yp < 1,
         'exact sign check using monotonicity of real log')
    equal('edge balance gives zero production', (x-x)*sp.log(x/x),0)

    # Full, free, NONCOMMUTING coefficient test of the derivative specialization.
    P = nc.P.atom('P')
    G = nc.symbols('GAP')
    X = nc.symbols('FIELDX')
    Y = nc.symbols('FIELDY')
    deriv = lambda z: nc.delta(P,z)
    def pair(D,g,z):
        a,b=z
        return nc.za(D(a),nc.zm(g,b)), nc.zs(nc.zm(g,a),D(b))
    first,second = pair(deriv,G,pair(deriv,G,(X,Y)))
    g2 = nc.zm(G,G)
    expected_first = nc.za(nc.zs(nc.za(deriv(deriv(X)),nc.zm(g2,X)),nc.assoc(G,G,X)),nc.zm(deriv(G),Y))
    expected_second = nc.zs(nc.zs(nc.za(deriv(deriv(Y)),nc.zm(g2,Y)),nc.assoc(G,G,Y)),nc.zm(deriv(G),X))
    equal('ordered coefficient bilayer square first',first,expected_first,'free noncommuting coefficient identity (8 entries)')
    equal('ordered coefficient bilayer square second',second,expected_second,'free noncommuting coefficient identity (8 entries)')
    H = nc.symbols('LOWERGAP')
    def two_pair(D,g,h,z):
        a,b=z
        return nc.za(D(a),nc.zm(g,b)),nc.zs(nc.zm(h,a),D(b))
    independent_first,independent_second=two_pair(deriv,G,H,two_pair(deriv,G,H,(X,Y)))
    expected_independent_first=nc.za(nc.zs(nc.za(deriv(deriv(X)),nc.zm(nc.zm(G,H),X)),nc.assoc(G,H,X)),nc.zm(deriv(G),Y))
    expected_independent_second=nc.zs(nc.zs(nc.za(deriv(deriv(Y)),nc.zm(nc.zm(H,G),Y)),nc.assoc(H,G,Y)),nc.zm(deriv(H),X))
    equal('independent ordered couplings first',independent_first,expected_independent_first,'free noncommuting coefficient identity (8 entries)')
    equal('independent ordered couplings second',independent_second,expected_independent_second,'free noncommuting coefficient identity (8 entries)')
    comm = nc.zs(deriv(nc.zm(G,X)),nc.zm(G,deriv(X)))
    equal('gap commutator uses actual Leibniz derivation',comm,nc.zm(deriv(G),X),'free noncommuting coefficient identity (8 entries)')
    bxy=pair(deriv,G,(X,Y)); byx=pair(deriv,G,(Y,X))
    equal('plain swap anticommutator first',nc.za(byx[0],bxy[1]),nc.za(nc.zm(G,X),nc.zm(G,X)),
          'free noncommuting coefficient identity (8 entries)')
    equal('plain swap anticommutator second',nc.za(byx[1],bxy[0]),nc.za(nc.zm(G,Y),nc.zm(G,Y)),
          'free noncommuting coefficient identity (8 entries)')

    # Arbitrary linear D, not a derivation: retain [D,L_G] instead of replacing it by D(G).
    gs=tuple(sp.symbols('g0:8')); xs=tuple(sp.symbols('x0:8')); ys=tuple(sp.symbols('y0:8'))
    M=sp.diag(*range(1,9)); M[0,3]=2; M[4,1]=-3
    D=lambda z: tuple(M*sp.Matrix(z))
    gapcomm=lambda z:nc.zs(D(nc.zm(gs,z)),nc.zm(gs,D(z)))
    left,right=pair(D,gs,pair(D,gs,(xs,ys)))
    gg=nc.zm(gs,gs)
    equal('arbitrary linear D square first',left,nc.za(nc.zs(nc.za(D(D(xs)),nc.zm(gg,xs)),nc.assoc(gs,gs,xs)),gapcomm(ys)))
    equal('arbitrary linear D square second',right,nc.zs(nc.zs(nc.za(D(D(ys)),nc.zm(gg,ys)),nc.assoc(gs,gs,ys)),gapcomm(xs)))
    true('arbitrary D need not satisfy the gap Leibniz rule',
         any(sp.expand(a-b)!=0 for a,b in zip(gapcomm(xs),nc.zm(D(gs),xs))),
         'exact polynomial counterexample')

    z,o=nc.zero,nc.one
    plus=(o,z,z,z,z,z,z,z);minus=(z,o,z,z,z,z,z,z);zero=(z,)*8
    equal('nonzero pole coupling zero mode first',pair(lambda _:zero,plus,(minus,zero))[0],zero,'exact zero-mode witness')
    equal('nonzero pole coupling zero mode second',pair(lambda _:zero,plus,(minus,zero))[1],zero,'exact zero-mode witness')
    true('coupling and zero-mode vector are nonzero',plus!=zero and minus!=zero,'exact witness nontriviality')

    z2=sp.zeros(2);eye=sp.eye(2);e12=sp.Matrix([[0,1],[0,0]]);e21=e12.T
    curved=(z2,z2,e12,e21,z2,z2,z2,z2);pole=(eye,z2,z2,z2,z2,z2,z2,z2)
    action_defect=nc.zs(nc.zm(nc.zm(curved,curved),pole),nc.zm(curved,nc.zm(curved,pole)))
    observed=(2*action_defect[7][0,0]+action_defect[7][1,1])/3
    equal('positive projective expectation detects square defect',observed,sp.Rational(1,3),'exact parent-witness reuse')

    J=sp.Matrix([[0,-1],[1,0]]);q=sp.Matrix(sp.symbols('u v'))
    a=sp.symbols('a',real=True)
    equal('real phase square',J*J,-sp.eye(2),'exact real-linear example')
    equal('real phase orthogonality',(q.T*J*q)[0],0,'exact real-linear example')
    equal('real eigenvalue polynomial',sp.det(J-a*sp.eye(2)),a*a+1,'exact real-linear example')

    report={'lean_kernel_verified':False,'status':'passed','check_count':len(checks),
            'checks':checks,'note':'Finite examples and independent polynomial identities are not Lean certificates.'}
    (ROOT/'reports').mkdir(exist_ok=True)
    (ROOT/'reports/projective-graph-zorn-bilayer-exact.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))

if __name__=='__main__':
    main()
