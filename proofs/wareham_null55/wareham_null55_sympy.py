#!/usr/bin/env python3
import sympy as sp

def q(x): return sp.simplify(x[0]**2-x[1]**2)
def b(x,y): return sp.simplify(x[0]*y[0]-x[1]*y[1])
def refl(x): return sp.Matrix([-x[0],x[1]])
e=sp.Matrix([1,0]); eb=sp.Matrix([0,1]); n=sp.Matrix([1,1]); nb=sp.Matrix([1,-1])
assert q(e)==1
assert q(eb)==-1
assert b(e,eb)==0
assert q(n)==0
assert q(nb)==0
assert b(n,nb)==2
assert refl(n)==-nb
assert refl(nb)==-n
m0=sp.Rational(0); dP=sp.Rational(1,4); dT=sp.Rational(1,25)
ms=m0*m0+dP+dT; mc=m0*m0+dP-dT
assert ms-mc==2*dT
assert ms != mc
print({'q_n':q(n),'q_nbar':q(nb),'n_dot_nbar':b(n,nb),'reflect_n':list(refl(n)),'mass_delta':ms-mc})
