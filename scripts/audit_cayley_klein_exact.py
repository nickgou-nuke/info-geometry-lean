#!/usr/bin/env python3
"""Exact independent algebra checks. This does NOT run or certify Lean proofs."""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import sympy as S


def zorn(a, v, w, b):
    return (a, S.Matrix(v), S.Matrix(w), b)


def add(X, Y):
    return tuple(x + y for x, y in zip(X, Y))


def scale(c, X):
    return tuple(c * x for x in X)


def mul(X, Y):
    a, v, w, b = X
    c, u, t, d = Y
    return zorn(a*c + v.dot(t), a*u + d*v - w.cross(t),
                c*w + b*t + v.cross(u), w.dot(u) + b*d)


def coords(X):
    return [X[0], *X[1], *X[2], X[3]]


def equal(X, Y):
    return all(S.cancel(x-y) == 0 for x,y in zip(coords(X),coords(Y)))


def norm(X):
    return X[0]*X[3] - X[1].dot(X[2])


def conjugate(X):
    return zorn(X[3], -X[1], -X[2], X[0])


def inv(X):
    return scale(1/norm(X), conjugate(X))


def core(A):
    return zorn(A[0,0],[A[0,1],0,0],[A[1,0],0,0],A[1,1])


I = zorn(S.Integer(1),[0,0,0],[0,0,0],S.Integer(1))
ell = zorn(0,[0,1,0],[0,1,0],0)


def split_double(A,B):
    return add(core(A),mul(core(B),ell))


def core_conj(A):
    return S.Matrix([[A[1,1],-A[0,1]],[-A[1,0],A[0,0]]])


def matrix_exponent(x,y):
    return (x[1]*y[0]+x[2]*y[2]) % 2


def split_exponent(x,y):
    return (x[1]*y[0]+x[2]*y[0]+x[2]*y[1]+x[2]*y[0]*y[1]
            +x[1]*y[0]*y[2]+x[0]*y[1]*y[2]) % 2


def parity(x,y,z):
    return sum(x[i]*y[j]*z[k] for i,j,k in itertools.permutations(range(3))) % 2


def plus(x,y):
    return tuple(a^b for a,b in zip(x,y))


def phi(f,x,y,z):
    return (-1)**((f(x,y)+f(plus(x,y),z)+f(y,z)+f(x,plus(y,z))) % 2)


def twist_exponent(x,y):
    return (split_exponent(x,y)+matrix_exponent(x,y)) % 2


def main():
    grades=list(itertools.product((0,1),repeat=3))
    p=S.diag(1,-1)
    q=S.Matrix([[0,1],[1,0]])
    def b(x): return p**x[0]*q**x[1]
    def mb(x): return S.I**x[2]*b(x)
    def zb(x): return split_double(b(x),S.zeros(2)) if x[2]==0 else split_double(S.zeros(2),b(x))
    for x,y in itertools.product(grades,repeat=2):
        assert mb(x)*mb(y)==(-1)**matrix_exponent(x,y)*mb(plus(x,y))
        assert equal(mul(zb(x),zb(y)),scale((-1)**split_exponent(x,y),zb(plus(x,y))))
    for x,y,z in itertools.product(grades,repeat=3):
        assert phi(matrix_exponent,x,y,z)==1
        assert phi(split_exponent,x,y,z)==(-1)**parity(x,y,z)
        assert phi(twist_exponent,x,y,z)==phi(split_exponent,x,y,z)
    for x,y,z,w in itertools.product(grades,repeat=4):
        assert (phi(twist_exponent,x,y,z)*phi(twist_exponent,x,plus(y,z),w)*phi(twist_exponent,y,z,w)
                ==phi(twist_exponent,plus(x,y),z,w)*phi(twist_exponent,x,y,plus(z,w)))
    A,B,C,D=(S.Matrix(2,2,S.symbols(f'{name}0:4',real=True)) for name in 'ABCD')
    assert equal(mul(split_double(A,B),split_double(C,D)),
                 split_double(A*C+core_conj(D)*B,D*A+B*core_conj(C)))
    assert S.simplify((A+S.I*B)*(C+S.I*D)-((A*C-B*D)+S.I*(A*D+B*C)))==S.zeros(2)
    vals=S.symbols('a v0 v1 v2 w0 w1 w2 b',real=True)
    X=zorn(vals[0],vals[1:4],vals[4:7],vals[7])
    assert equal(mul(X,inv(X)),I)
    assert equal(mul(inv(X),X),I)
    assert S.expand(norm(add(X,I))-norm(X)-X[0]-X[3]-1)==0
    a,b=S.symbols('a b')
    Z=zorn(a,[0,0,0],[0,0,0],b)
    assert equal(mul(add(Z,scale(-1,I)),inv(add(Z,I))),
                 zorn((a-1)/(a+1),[0,0,0],[0,0,0],(b-1)/(b+1)))
    s,z,a,y=S.symbols('s z a y')
    cayley=lambda v:(v-1)/(v+1)
    ber=lambda v:(1+v)/(1-v)
    assert S.cancel(cayley(z)-(2*z/(1+z)-1))==0
    assert S.cancel(ber(z)+1/cayley(z))==0
    assert S.cancel(ber(s/(1-s))+1/(2*s-1))==0
    assert S.cancel((s-S.Rational(1,2))*(-1/(2*s-1))+S.Rational(1,2))==0
    assert S.cancel(cayley(a*a)-(a-1/a)/(a+1/a))==0
    assert S.cancel(-1/(2*(S.Rational(1,2)+S.I*y)-1)-S.I/(2*y))==0
    result={
        'method':'Exact integer enumeration and SymPy rational/polynomial identities',
        'matrix_native_products':64,'zorn_native_products':64,
        'associative_source_triples':512,'split_associator_triples':512,
        'relative_coboundary_triples':512,'pentagon_quadruples':4096,
        'symbolic_doubling_laws':2,'native_inverse_sides':2,
        'native_cayley_diagonal':True,'scalar_cayley_berezinian_checks':True,
        'all_checks_passed':True,'lean_kernel_executed':False,
        'caveat':'Rational identities checked on their regular domains. Not an elaboration or transitive axiom audit.'}
    out=Path(__file__).resolve().parents[1]/'reports'/'exact-algebra-checks.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
