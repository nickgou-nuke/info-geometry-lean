#!/usr/bin/env python3
"""Exact independent algebra checks. These do not execute Lean."""
from __future__ import annotations
import json
import random
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[1]
checks: dict[str, int] = {}

def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    checks[name] = checks.get(name, 0) + 1

def zero_for(x):
    return s.zeros(*x.shape) if isinstance(x, s.MatrixBase) else s.Integer(0)

def cross(u, v):
    return [u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0]]

def dot(u, v):
    return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]

def mul(x, y):
    a,b,u,v = x
    c,d,w,z = y
    vz,uw=cross(v,z),cross(u,w)
    return (a*c+dot(u,z), b*d+dot(v,w),
            [a*w[i]+u[i]*d-vz[i] for i in range(3)],
            [b*z[i]+v[i]*c+uw[i] for i in range(3)])

def flip(x):
    a,b,u,v=x
    return a,b,[-t for t in u],[-t for t in v]

def swap(x):
    a,b,u,v=x
    return b,a,list(v),list(u)

def signed_swap(x):
    return swap(flip(x))

def entries(x):
    return [x[0],x[1],*x[2],*x[3]]

def same(x,y):
    return all(s.expand(a-b)==0 for a,b in zip(entries(x),entries(y)))

def quad(x):
    return x[0]*x[1]-dot(x[2],x[3])

# Universal identities in a free noncommutative coefficient algebra.
a,b,c,d=s.symbols('a b c d', commutative=False)
u=s.symbols('u0:3',commutative=False); v=s.symbols('v0:3',commutative=False)
w=s.symbols('w0:3',commutative=False); z=s.symbols('z0:3',commutative=False)
X=(a,b,u,v); Y=(c,d,w,z)
check('free_noncommutative_signed_exchange_product', same(signed_swap(mul(X,Y)),mul(signed_swap(X),signed_swap(Y))))
check('coordinate_actions_commute',same(flip(swap(X)),swap(flip(X))))
for action in (flip,swap,signed_swap):
    check('coordinate_involution',same(action(action(X)),X))
comm_defect=b*a-a*b+sum((u[i]*v[i]-v[i]*u[i] for i in range(3)),s.Integer(0))
check('ordered_readout_exact_commutator_defect',s.expand(quad(signed_swap(X))-quad(X)-comm_defect)==0)
check('coordinate_sign_ordered_readout',s.expand(quad(flip(X))-quad(X))==0)

# Scalar basis tests, including the two invalid component automorphisms.
basis=[]
for i in range(8):
    q=[s.Integer(int(i==j)) for j in range(8)]
    basis.append((q[0],q[1],q[2:5],q[5:8]))
for x in basis:
    for y in basis:
        check('scalar_basis_product_covariance',same(signed_swap(mul(x,y)),mul(signed_swap(x),signed_swap(y))))
x,y=basis[2],basis[3]
check('sign_not_product_preserving',not same(flip(mul(x,y)),mul(flip(x),flip(y))))
check('plain_exchange_not_product_preserving',not same(swap(mul(x,y)),mul(swap(x),swap(y))))
check('null_idempotent_not_square_zero',quad(basis[0])==0 and same(mul(basis[0],basis[0]),basis[0]))

# Native scalar quadratic polarization and positive fundamental symmetry.
xs=s.symbols('x0:8',real=True); ys=s.symbols('y0:8',real=True)
XX=(xs[0],xs[1],xs[2:5],xs[5:8]); YY=(ys[0],ys[1],ys[2:5],ys[5:8])
def polar(x,y):
    return (x[0]*y[1]+x[1]*y[0]-dot(x[2],y[3])-dot(x[3],y[2]))/2
check('scalar_norm_preservation',s.expand(quad(signed_swap(XX))-quad(XX))==0)
check('scalar_positive_hilbertization',s.expand(polar(XX,signed_swap(YY))-sum(xs[i]*ys[i] for i in range(8))/2)==0)
G=s.Matrix.hstack(*(s.Matrix(entries(signed_swap(x))) for x in basis))
B=s.hessian(quad(XX),xs)/2
check('scalar_polar_signature_4_4',B.eigenvals()=={s.Rational(1,2):4,-s.Rational(1,2):4})
check('scalar_fundamental_matrix',B*G==s.eye(8)/2)
check('scalar_signed_exchange_determinant_plus_one',G.det()==1)

# Source ten-coordinate layout: no octonionic multiplication is postulated.
q=s.symbols('q0:10',real=True)
Q=q[0]*q[5]-q[1]*q[6]+q[2]*q[7]+q[3]*q[8]+q[4]*q[9]
B10=s.hessian(Q,q)/2
qG=s.Matrix([q[5],-q[6],-q[7],-q[8],-q[9],q[0],-q[1],-q[2],-q[3],-q[4]])
G10=qG.jacobian(q)
check('source_signature_5_5',B10.eigenvals()=={s.Rational(1,2):5,-s.Rational(1,2):5})
check('source_signed_exchange_involution',G10*G10==s.eye(10))
check('source_signed_exchange_determinant_minus_one',G10.det()==-1)
check('source_signed_exchange_not_positive',(B10*G10)[2,2]==-s.Rational(1,2))
p=s.symbols('p0:5',real=True); r=s.symbols('r0:5',real=True)
check('five_pair_diagonal_normal_form',s.expand(sum(p[i]*r[i] for i in range(5))-sum(((p[i]+r[i])/2)**2-((p[i]-r[i])/2)**2 for i in range(5)))==0)

# Actual noncommuting 2x2 coefficients.
Z=s.zeros(2); K=s.diag(1,-1); J=s.Matrix([[0,1],[1,0]])
U=[Z,K,J]; op=(Z,Z,U,[Z,Z,Z]); op2=mul(op,op)
check('operator_upper_null',quad(op)==Z)
check('operator_upper_square_nonzero',op2[3][0]==K*J-J*K and op2[3][0]!=Z)
check('implementers_anticommute',K*J==-J*K)
check('implementer_square_minus_one',(J*K)**2==-s.eye(2))
M=s.Matrix(2,2,s.symbols('m0:4'))
check('conjugation_actions_commute',K*(J*M*J)*K==J*(K*M*K)*J)
check('composite_conjugation_square',(J*K)*((J*K)*M*(K*J))*(K*J)==M)

rng=random.Random(154)
for _ in range(64):
    mm=[s.Matrix(2,2,[rng.randrange(-3,4) for _ in range(4)]) for _ in range(8)]
    xx=(mm[0],mm[1],mm[2:5],mm[5:8])
    check('matrix_trace_signed_exchange',s.trace(quad(signed_swap(xx)))==s.trace(quad(xx)))
    cr=cross(xx[2],xx[2]); zz=mul((Z,Z,xx[2],[Z]*3),(Z,Z,xx[2],[Z]*3))
    check('matrix_square_zero_iff_commuting',all(a==Z for a in entries(zz))==all(a==Z for a in cr))

# Product of boundary coefficients is a rank-one numerator, not the overlap.
v0=s.Matrix([1,s.I]); pre=s.Matrix([2,1]); post=s.Matrix([1,2*s.I])
f=s.Matrix([[3,1-s.I]]); bra=post.conjugate().T
probe=v0*f; ov=(bra*pre)[0]
check('rank_one_coefficient_factorization',s.expand((bra*probe*pre)[0]-(bra*v0)[0]*(f*pre)[0])==0)
P=pre*bra/ov
check('boundary_projection',s.simplify(P*P-P)==s.zeros(2))
check('rank_one_weak_compression',s.simplify(P*probe*P-((bra*probe*pre)[0]/ov)*P)==s.zeros(2))
check('boundary_probe_dependence',ov!=0 and (bra*s.zeros(2)*pre)[0]/ov==0 and s.simplify((bra*pre)[0]/ov)==1)

report={'status':'PASS','evidence':'independent exact symbolic/arithmetic tests; NOT Lean kernel verification',
        'assertions':sum(checks.values()),'families':checks}
out=ROOT/'reports'/'exact-checks.json'; out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
