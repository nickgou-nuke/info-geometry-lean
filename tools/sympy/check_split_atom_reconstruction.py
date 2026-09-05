#!/usr/bin/env python3
"""Exact symbolic regression checks; these do not elaborate or verify Lean proofs."""
from __future__ import annotations
import json
import sympy as s

checks: list[str] = []

def check(name: str, expression: object) -> None:
    entries = list(expression) if isinstance(expression, s.MatrixBase) else [expression]
    if any(s.simplify(e) != 0 for e in entries):
        raise AssertionError(f"Identity failed: {name}: {expression}")
    checks.append(name)

def matrix(prefix: str) -> s.Matrix:
    return s.Matrix(2, 2, s.symbols(f"{prefix}0:4", real=True))

I=s.Matrix([[0,1],[-1,0]]); J=s.diag(1,-1); K=I*J; one=s.eye(2)
A=matrix('a'); B=matrix('b'); U=matrix('u')
for name, expr in [('I_sq',I*I+one), ('J_sq',J*J-one), ('K_sq',K*K-one),
                   ('IJ',I*J-K), ('JI',J*I+K), ('JK',J*K+I),
                   ('KJ',K*J-I), ('KI',K*I-J), ('IK',I*K+J)]: check(name,expr)
P=(one+J)/2; Q=(one-J)/2
check('Peirce four blocks', A-(P*A*P+P*A*Q+Q*A*P+Q*A*Q))
check('raising nilpotent', (I-K)/2-s.Matrix([[0,1],[0,0]]))
grade=lambda X:K*X*K
rev=lambda X:J*X.T*J
conj=lambda X:-I*X.T*I
check('grade automorphism',grade(A*B)-grade(A)*grade(B))
check('reversion antimultiplicative',rev(A*B)-rev(B)*rev(A))
check('reversion involutive',rev(rev(A))-A)
check('Clifford conjugation',conj(A)-grade(rev(A)))
check('determinant composition',A*conj(A)-A.det()*one)
g=lambda X,Y:(X[0,0]*Y[1,1]+X[1,1]*Y[0,0]-X[0,1]*Y[1,0]-X[1,0]*Y[0,1])/2
check('metric self',g(A,A)-A.det())
check('metric symmetry',g(A,B)-g(B,A))
check('metric left scaling',g(U*A,U*B)-U.det()*g(A,B))
a,b,c,d=s.symbols('a b c d', real=True)
check('signature 2,2',g(a*one+b*I+c*J+d*K,a*one+b*I+c*J+d*K)-(a*a+b*b-c*c-d*d))
for name,u in [('I',I),('J',J),('K',K)]: check(f'omega {name} alternating',g(u*A,A))
assert g(K,K)==-1 and g(K*K,one)==1
checks.append('omega K nonsymmetry witnesses')
z=s.symbols('z', nonzero=True)
f=lambda z:1/z-1/(z-1)
tau=lambda z:1-z
sig=lambda z:1/z
check('puncture braid',tau(sig(tau(z)))-sig(tau(sig(z))))
check('puncture cycle',tau(sig(tau(sig(tau(sig(z))))))-z)
check('logarithmic normal form',f(z)+1/(z*(z-1)))
check('logarithmic derivative',s.diff(z/(z-1),z)/(z/(z-1))-f(z))
check('exchange pullback',-f(1-z)+f(z))
check('inversion pullback',f(1/z)*(-1/z**2)+1/(z-1))
S=s.Matrix([[0,-1],[1,0]]); T=s.Matrix([[1,1],[0,1]])
check('modular S square',S*S+one); check('modular ST cube',(S*T)**3+one)
p,q=s.symbols('p q', positive=True)
rho=s.diag(p,q); inv=s.diag(1/p,1/q)
check('physical upper boundary',s.trace(rho*A*rho*B*inv)-s.trace(rho*B*A))
check('modular upper boundary',s.trace(rho*inv*A*rho*B)-s.trace(rho*B*A))
C=s.Matrix(2,2,[s.Symbol(f'r{k}',real=True)+s.I*s.Symbol(f'i{k}',real=True) for k in range(4)])
check('state square imaginary part',s.im(s.trace(rho*C.conjugate().T*C)))
R=s.Matrix(2,3,s.symbols('r0:6',real=True)); x=s.Matrix(s.symbols('x0:3',real=True))
check('Gram production', (x.T*R.T*R*x)[0]-sum(v*v for v in R*x))
AA=s.Matrix(3,3,s.symbols('c0:9',real=True))
check('skew production',(x.T*(AA-AA.T)*x)[0])
Z=s.zeros(2)
twist=lambda M:s.BlockMatrix([[M,Z],[Z,-M]]).as_explicit()
repeat=lambda M:s.BlockMatrix([[M,Z],[Z,M]]).as_explicit()
pos=s.BlockMatrix([[Z,one],[one,Z]]).as_explicit()
neg=s.BlockMatrix([[Z,one],[-one,Z]]).as_explicit()
check('twisted product',twist(A)*twist(B)-repeat(A*B))
check('twisted positive anticommutator',twist(A)*pos+pos*twist(A))
check('twisted negative anticommutator',twist(A)*neg+neg*twist(A))
v=s.Matrix([s.Symbol('v0',complex=True),s.Symbol('v1',complex=True)])
ph=lambda v:s.Matrix([s.conjugate(v[1]),s.conjugate(v[0])])
e=s.Symbol('e',real=True); H=s.diag(e,-e)
check('particle-hole involution',ph(ph(v))-v)
check('particle-hole covariance',ph(H*v)+H*ph(v))
print(json.dumps({'check_kind':'exact symbolic regression, NOT Lean kernel verification',
    'lean_kernel_checked':False,'passed':len(checks),'checks':checks},indent=2))
