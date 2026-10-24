#!/usr/bin/env python3
"""Exact Pauli-block twisted product audit; not paper authentication or Lean proof."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import sympy as s

ROOT = Path(__file__).resolve().parents[2]
path = ROOT / 'tools/sympy/split_octonion_multiplication.py'
spec = importlib.util.spec_from_file_location('gg_pauli_zorn', path)
z = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = z
spec.loader.exec_module(z)
I2 = s.eye(2)

def sigma(u):
    return s.Matrix([[u[2],u[0]-s.I*u[1]],[u[0]+s.I*u[1],-u[2]]])

def block(A,B,C,D):
    return A.row_join(B).col_join(C.row_join(D))

def encode(X):
    return block(X.a*I2,-s.I*sigma(X.x),s.I*sigma(X.y),X.b*I2)

def twist(A,B):
    P,Q,U,V = A[:2,2:],A[2:,:2],B[:2,2:],B[2:,:2]
    a,b,c,d = A[0,0],A[2,2],B[0,0],B[2,2]
    return block((a*c+s.trace(P*V)/2)*I2,
                 a*U+d*P-(Q*V-V*Q)/2,
                 c*Q+b*V-(P*U-U*P)/2,
                 (b*d+s.trace(Q*U)/2)*I2)

for X in z.BASIS:
    for Y in z.BASIS:
        assert (twist(encode(X),encode(Y))-encode(X*Y)).applyfunc(s.expand)==s.zeros(4)
x,y=s.symbols('x0:8'),s.symbols('y0:8')
X,Y=z.Zorn(x[0],x[1],x[2:5],x[5:8]),z.Zorn(y[0],y[1],y[2:5],y[5:8])
assert (twist(encode(X),encode(Y))-encode(X*Y)).applyfunc(s.expand)==s.zeros(4)
assert encode(z.UP[0])*encode(z.UP[1])==s.zeros(4)
assert twist(encode(z.UP[0]),encode(z.UP[1]))==encode(z.DOWN[2]) != s.zeros(4)
gamma5=s.diag(-1,-1,1,1)
assert encode(z.EPLUS)==(s.eye(4)-gamma5)/2
assert encode(z.EMINUS)==(s.eye(4)+gamma5)/2
expected_det=(X.a*X.b)**2-2*X.a*X.b*z.dot(X.x,X.y)+z.dot(X.x,X.x)*z.dot(X.y,X.y)
assert s.expand(encode(X).det()-expected_det)==0
witness=z.UP[0]+z.DOWN[1]
assert witness.det()==0 and encode(witness).det()==1
print(json.dumps({'basis':['E11','E22','U0','U1','U2','V0','V1','V2'],
 'coordinate_order':['a','b','upper0','upper1','upper2','lower0','lower1','lower2'],
 'ring':'QQ(i), exact', 'basis_product_checks':64,'symbolic_product':'PASS',
 'ordinary_vs_twisted_product_obstruction':'PASS','chiral_projectors':'PASS',
 'ordinary_determinant_formula':'PASS','ordinary_determinant_is_not_squared_Zorn_norm':'PASS',
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'multiplication_source_sha256':hashlib.sha256(path.read_bytes()).hexdigest()},sort_keys=True,indent=2))
