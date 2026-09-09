#!/usr/bin/env python3
"""Exact free-associative-coefficient regression, NOT a Lean certificate.

Zorn products remain nonassociative; only coefficient words are associative.
The two letters g/G are mutual inverses. All other letters are free and
noncommuting. Equality is checked coefficient-by-coefficient, without floats.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path

@dataclass(frozen=True)
class P:
    terms: dict[tuple[str, ...], Fraction]
    @staticmethod
    def scalar(n: int) -> P:
        return P({(): Fraction(n)} if n else {})
    @staticmethod
    def atom(s: str) -> P:
        return P({(s,): Fraction(1)})
    def __add__(self, other: P) -> P:
        out = self.terms.copy()
        for w, c in other.terms.items():
            out[w] = out.get(w, Fraction(0)) + c
            if not out[w]: del out[w]
        return P(out)
    def __neg__(self) -> P:
        return P({w: -c for w, c in self.terms.items()})
    def __sub__(self, other: P) -> P:
        return self + (-other)
    def __mul__(self, other: P) -> P:
        out: dict[tuple[str, ...], Fraction] = {}
        for a, ca in self.terms.items():
            for b, cb in other.terms.items():
                stack: list[str] = []
                for x in a + b:
                    if stack and (stack[-1], x) in {('g', 'G'), ('G', 'g')}:
                        stack.pop()
                    else: stack.append(x)
                w = tuple(stack)
                out[w] = out.get(w, Fraction(0)) + ca * cb
                if not out[w]: del out[w]
        return P(out)

Z = tuple[P, ...]
zero, one = P.scalar(0), P.scalar(1)
def za(x: Z, y: Z) -> Z: return tuple(a+b for a,b in zip(x,y))
def zn(x: Z) -> Z: return tuple(-a for a in x)
def zs(x: Z, y: Z) -> Z: return za(x,zn(y))
def dot(u: Z, v: Z) -> P: return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]
def cross(u: Z, v: Z) -> Z:
    return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def zm(x: Z, y: Z) -> Z:
    if len(x) != 8 or len(y) != 8:
        raise ValueError('Zorn values have exactly eight coefficient entries')
    a,b,u,v = x[0],x[1],x[2:5],x[5:8]
    c,d,w,t = y[0],y[1],y[2:5],y[5:8]
    vt,uw = cross(v,t),cross(u,w)
    return (a*c+dot(u,t),b*d+dot(v,w),
            *(a*w[i]+u[i]*d-vt[i] for i in range(3)),
            *(b*t[i]+v[i]*c+uw[i] for i in range(3)))
def cb(p: P, q: P) -> P: return p*q-q*p
def bracket(x: Z, y: Z) -> Z: return zs(zm(x,y),zm(y,x))
def assoc(x: Z, y: Z, z: Z) -> Z: return zs(zm(zm(x,y),z),zm(x,zm(y,z)))
def delta(p: P, x: Z) -> Z: return tuple(cb(p,a) for a in x)
def alt(x: Z,y: Z,z: Z) -> Z:
    return zs(zs(zs(za(za(assoc(x,y,z),assoc(y,z,x)),assoc(z,x,y)),assoc(y,x,z)),assoc(z,y,x)),assoc(x,z,y))
def cov(p: P,a: Z,x: Z) -> Z: return za(delta(p,x),zm(a,x))
def adj(p: P,a: Z,x: Z) -> Z: return za(delta(p,x),bracket(a,x))
def field(p: P,q: P,a: Z,b: Z) -> Z: return za(zs(delta(p,b),delta(q,a)),bracket(a,b))
def curv(p: P,q: P,a: Z,b: Z,x: Z) -> Z: return zs(cov(p,a,cov(q,b,x)),cov(q,b,cov(p,a,x)))
def symbols(s: str) -> Z: return tuple(P.atom(f'{s}{i}') for i in range(8))
g,gi=P.atom('g'),P.atom('G')
def cg(p: P) -> P: return g*p*gi
def gauge(x: Z) -> Z: return tuple(cg(a) for a in x)

def main() -> None:
    x,y,z=symbols('x'),symbols('y'),symbols('z')
    a,b,c=symbols('a'),symbols('b'),symbols('c')
    p,q,r=map(P.atom,('p','q','r'))
    checks=[]
    def check(name: str, left: Z|P, right: Z|P) -> None:
        if isinstance(left,P): left=(left,)
        if isinstance(right,P): right=(right,)
        assert len(left)==len(right)
        for i,(v,w) in enumerate(zip(left,right)):
            if v != w: raise AssertionError(f'{name}, coordinate {i}: nonzero defect')
        checks.append({'name':name,'coordinate_checks':len(left),'passed':True})
    check('coefficient_deriv_add',delta(p,za(x,y)),za(delta(p,x),delta(p,y)))
    check('coefficient_deriv_sub',delta(p,zs(x,y)),zs(delta(p,x),delta(p,y)))
    check('coefficient_deriv_product_rule',delta(p,zm(x,y)),za(zm(delta(p,x),y),zm(x,delta(p,y))))
    check('coefficient_deriv_commutator',zs(delta(p,delta(q,x)),delta(q,delta(p,x))),delta(cb(p,q),x))
    check('field_strength_swap',field(q,p,b,a),zn(field(p,q,a,b)))
    check('full_curvature',curv(p,q,a,b,x),za(zs(za(delta(cb(p,q),x),zm(field(p,q,a,b),x)),assoc(a,b,x)),assoc(b,a,x)))
    jac=za(za(bracket(x,bracket(y,z)),bracket(y,bracket(z,x))),bracket(z,bracket(x,y)))
    check('right_Akivis_identity',jac,zn(alt(x,y,z)))
    bia=za(za(adj(p,a,field(q,r,b,c)),adj(q,b,field(r,p,c,a))),adj(r,c,field(p,q,a,b)))
    check('full_Bianchi_with_both_sources',bia,zs(za(za(delta(cb(p,q),c),delta(cb(q,r),a)),delta(cb(r,p),b)),alt(a,b,c)))
    check('gauge_preserves_Zorn_product',gauge(zm(x,y)),zm(gauge(x),gauge(y)))
    check('gauge_preserves_associator',gauge(assoc(x,y,z)),assoc(gauge(x),gauge(y),gauge(z)))
    check('inhomogeneous_generator',cg(p),p-cb(p,g)*gi)
    check('gauge_covariant_derivative',gauge(cov(p,a,x)),cov(cg(p),gauge(a),gauge(x)))
    check('gauge_field_strength',gauge(field(p,q,a,b)),field(cg(p),cg(q),gauge(a),gauge(b)))
    check('gauge_full_curvature',gauge(curv(p,q,a,b,x)),curv(cg(p),cg(q),gauge(a),gauge(b),gauge(x)))
    check('operator_cross_self',cross((p,q,r),(p,q,r)),(cb(q,r),cb(r,p),cb(p,q)))
    u=(zero,zero,p,q,zero,zero,zero,zero)
    pole=(one,zero,zero,zero,zero,zero,zero,zero)
    defect=assoc(u,u,pole)
    check('alternativity_defect',defect,(zero,zero,zero,zero,zero,zero,zero,cb(p,q)))
    assert defect != (zero,)*8
    report={'status':'passed','method':'exact free noncommuting coefficient words; Zorn product not reassociated',
            'lean_kernel_verified':False,'identities':len(checks),
            'coordinate_checks':sum(c['coordinate_checks'] for c in checks),'checks':checks}
    root=Path(__file__).resolve().parents[2]
    dest=root/'reports'/'operator-zorn-gauge-algebra-checks.json'
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in report.items() if k!='checks'}))
if __name__=='__main__': main()
