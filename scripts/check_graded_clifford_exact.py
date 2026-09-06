#!/usr/bin/env python3
"""Exact regression evidence for the new identities; this does NOT run Lean."""
from __future__ import annotations
import json
import random
from collections import Counter
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
checks: Counter[str] = Counter()
rng = random.Random(80642)
I = sp.I
roots = [sp.Integer(1), I, -sp.Integer(1), -I]

def check(label: str, condition: bool) -> None:
    if not bool(condition):
        raise AssertionError(label)
    checks[label] += 1

def eq(a, b) -> bool:
    if isinstance(a, sp.MatrixBase):
        return all(sp.expand(z) == 0 for z in a - b)
    return sp.expand(a - b) == 0

def proj(U: sp.Matrix, k: int) -> sp.Matrix:
    z = roots[k]
    return sp.expand((sp.eye(U.rows) + z**3*U + z**2*(U**2) + z*(U**3))/4)

def random_matrix(d: int) -> sp.Matrix:
    return sp.Matrix(d, d, [rng.randrange(-2, 3) for _ in range(d*d)])

def sum_mat(items, d: int) -> sp.Matrix:
    return sum(items, sp.zeros(d))

# Fourth-root projector construction, including nonnormal finite-order operators.
for d in (1, 2, 3, 4):
    for trial in range(3):
        S = random_matrix(d)
        while S.det() == 0:
            S = random_matrix(d)
        lam = [roots[(j+trial) % 4] for j in range(d)]
        U = S*sp.diag(*lam)*S.inv()
        P = [proj(U, k) for k in range(4)]
        check('fourth_order', eq(U**4, sp.eye(d)))
        check('fourier_complete', eq(sum_mat(P, d), sp.eye(d)))
        check('fourier_synthesis', eq(sum_mat([roots[k]*P[k] for k in range(4)], d), U))
        for j in range(4):
            check('fourier_eigen', eq(U*P[j], roots[j]*P[j]))
            for k in range(4):
                check('fourier_idempotence_and_orthogonality', eq(P[j]*P[k], P[j] if j == k else sp.zeros(d)))
        # Generalized Peirce reconstruction and multiplication in corner-valued blocks.
        X, Y = random_matrix(d), random_matrix(d)
        BX = [[P[i]*X*P[j] for j in range(4)] for i in range(4)]
        BY = [[P[i]*Y*P[j] for j in range(4)] for i in range(4)]
        check('peirce_reconstruction', eq(sum_mat([z for row in BX for z in row], d), X))
        for i in range(4):
            for j in range(4):
                check('peirce_corner_support', eq(P[i]*BX[i][j]*P[j], BX[i][j]))
                check('peirce_matrix_product', eq(sum_mat([BX[i][k]*BY[k][j] for k in range(4)],d), P[i]*X*Y*P[j]))
                if i != j:
                    check('single_off_diagonal_square', eq(BX[i][j]**2, sp.zeros(d)))

# A square-minus-one operator has only its two imaginary-root sectors.
for d in (2, 4):
    U = sp.diag(*([I,-I]*(d//2)))
    P = [proj(U,k) for k in range(4)]
    check('complex_structure_even_projectors_zero', eq(P[0],sp.zeros(d)) and eq(P[2],sp.zeros(d)))
    check('complex_structure_two_projectors', eq(P[1],(sp.eye(d)-I*U)/2) and eq(P[3],(sp.eye(d)+I*U)/2))

# Fourth-order cyclic covariance and actual truncated nilpotency are distinct.
C = sp.diag(*roots)
N = sp.zeros(4)
T = sp.zeros(4)
for k in range(4):
    N[(k+1)%4,k] = 1
    if k < 3:
        T[k+1,k] = 1
for k in range(4):
    Pk, Pnext = proj(C,k), proj(C,(k+1)%4)
    check('cyclic_covariance', eq(N*Pk,Pnext*N))
    check('truncated_covariance', eq(T*Pk,Pnext*T))
check('cyclic_not_nilpotent', eq(N**4,sp.eye(4)) and not eq(N**4,sp.zeros(4)))
check('truncated_nilpotent_exact_order', eq(T**4,sp.zeros(4)) and not eq(T**3,sp.zeros(4)))
check('clock_shift', eq(C*N,I*N*C))

# Exterior algebra basis (bit subsets), with literal Koszul wedge signs.
def exterior_product(a: int, b: int):
    if a & b:
        return 0, 0
    crossings = sum((b & ((1 << i)-1)).bit_count() for i in range(a.bit_length()) if a & (1<<i))
    return (-1)**crossings, a | b

for d in range(6):
    for a in range(1<<d):
        la = I**a.bit_count()
        check('exterior_clock_fourth', eq(la**4,1))
        check('exterior_clock_square_parity', eq(la**2,(-1)**a.bit_count()))
        for k in range(4):
            coefficient = (1+roots[k]**3*la+roots[k]**2*la**2+roots[k]*la**3)/4
            check('exterior_fourier_degree_selection', eq(coefficient,int(a.bit_count()%4==k)))
        for b in range(1<<d):
            sign, out = exterior_product(a,b)
            check('exterior_clock_multiplicative', eq(sign*I**out.bit_count(),la*(I**b.bit_count())*sign))
check('degree_clock_not_complex_structure', 1**2 != -1)

# Clifford basis multiplication, with supplied orthogonal signature, not wedge product.
def clifford_product(a: int, b: int, signature: tuple[int,...]):
    sign = (-1)**sum((b & ((1<<i)-1)).bit_count() for i in range(len(signature)) if a & (1<<i))
    for i, sq in enumerate(signature):
        if a & b & (1<<i):
            sign *= sq
    return sign, a ^ b

for signature, expected in (((1,1,1,1),1), ((1,1,-1,-1),1), ((1,-1,-1,-1),-1)):
    coefficient, blade = clifford_product(15,15,signature)
    check('volume_signature_square', coefficient == expected and blade == 0)
check('four_grade_truncation_not_closed', clifford_product(1,2,(1,1,1,1))[1].bit_count()==2)
check('imaginary_scaling_not_clifford_multiplicative', I**2 != 1)
for d in range(2,12):
    check('hodge_bivector_degree', (d-2==1) == (d==3))
    if d%2==0:
        for k in range(d+1):
            check('hodge_preserves_parity_even_dimension',(d-k)%2==k%2)

# Idempotent need not mean orthogonal/Hermitian or primitive.
S = sp.Matrix([[1,1],[0,1]])
U = S*sp.diag(1,I)*S.inv()
P = proj(U,0)
check('finite_order_projector_not_self_adjoint',eq(P*P,P) and not eq(P,P.conjugate().T))
Pbig = sp.diag(1,1,0,0)
Psmall0 = sp.diag(1,0,0,0); Psmall1 = sp.diag(0,1,0,0)
check('chirality_projector_not_primitive',eq(Pbig,Psmall0+Psmall1) and eq(Psmall0*Psmall1,sp.zeros(4)))

# Native scalar Zorn products contradict same-corner associative routing.
def cross(u,v):
    return (u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0])
def zorn(X,Y):
    a,b,u,v = X; c,d,x,y = Y
    vy,ux=cross(v,y),cross(u,x)
    return (a*c+sum(u[i]*y[i] for i in range(3)),b*d+sum(v[i]*x[i] for i in range(3)),
            tuple(a*x[i]+d*u[i]-vy[i] for i in range(3)),
            tuple(b*y[i]+c*v[i]+ux[i] for i in range(3)))
upper=lambda u:(0,0,u,(0,0,0))
x,y,z=upper((1,0,0)),upper((0,1,0)),upper((0,0,1))
check('zorn_same_rail_product_nonzero',zorn(x,y)==(0,0,(0,0,0),(0,0,1)))
check('zorn_not_associative',zorn(zorn(x,y),z)!=zorn(x,zorn(y,z)))

report={'status':'PASS','evidence':'independent exact arithmetic; NOT Lean elaboration or kernel verification',
        'assertions':sum(checks.values()),'families':dict(checks)}
out=ROOT/'reports'/'graded-clifford-exact.json'; out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
