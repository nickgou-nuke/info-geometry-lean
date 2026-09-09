#!/usr/bin/env python3
"""Independent exact regression checks; this does not execute or certify Lean."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[1]

def assert_zero(expr):
    assert s.expand(expr) == 0, expr

def coordinates(z):
    a,b,t,u1,u2,u3,r,v1,v2,v3=z
    return s.Matrix([(a+b)/2,(t-r)/2,(u1+v1)/2,(u2+v2)/2,(u3+v3)/2,
                     (a-b)/2,(t+r)/2,(u1-v1)/2,(u2-v2)/2,(u3-v3)/2])

def inverse(w):
    p=w[:5];n=w[5:]
    return s.Matrix([p[0]+n[0],p[0]-n[0],p[1]+n[1],p[2]+n[2],p[3]+n[3],p[4]+n[4],
                     n[1]-p[1],p[2]-n[2],p[3]-n[3],p[4]-n[4]])

def q(z):
    a,b,t,u1,u2,u3,r,v1,v2,v3=z
    return a*b-t*r+u1*v1+u2*v2+u3*v3

def polar(x,y): return s.expand(q(x+y)-q(x)-q(y))
def swap(z): return s.Matrix([z[1],z[0],z[6],z[7],z[8],z[9],z[2],z[3],z[4],z[5]])
def flip(z): return s.diag(1,1,-1,-1,-1,-1,-1,-1,-1,-1)*z

def fundamental(z):
    return s.Matrix([z[1],z[0],-z[6],z[7],z[8],z[9],-z[2],z[3],z[4],z[5]])

def wedge(u,v):
    return s.Matrix([u[0]*v[1]-u[1]*v[0],u[0]*v[2]-u[2]*v[0],u[0]*v[3]-u[3]*v[0],
                     u[2]*v[3]-u[3]*v[2],u[3]*v[1]-u[1]*v[3],u[1]*v[2]-u[2]*v[1]])

def main():
    z=s.Matrix(s.symbols('a b t u1 u2 u3 r v1 v2 v3',real=True))
    w=s.Matrix(s.symbols('w0:10',real=True))
    assert inverse(coordinates(z)).applyfunc(s.expand)==z
    assert coordinates(inverse(w)).applyfunc(s.expand)==w
    assert_zero(sum(v*v for v in coordinates(z)[:5])-sum(v*v for v in coordinates(z)[5:])-q(z))
    swap_matrix=s.diag(1,-1,1,1,1,-1,1,-1,-1,-1)
    assert (coordinates(swap(z))-swap_matrix*coordinates(z)).applyfunc(s.expand)==s.zeros(10,1)
    assert swap_matrix.det()==-1
    for f in (swap,flip,lambda x:swap(flip(x)),fundamental):
        assert_zero(q(f(z))-q(z))
        assert (f(f(z))-z).applyfunc(s.expand)==s.zeros(10,1)
    assert (coordinates(fundamental(z))-s.diag(1,1,1,1,1,-1,-1,-1,-1,-1)*coordinates(z)).applyfunc(s.expand)==s.zeros(10,1)
    assert_zero(polar(z,fundamental(z))-sum(a*a for a in z))
    witness=s.Matrix([1,-1,0,0,0,0,0,0,0,0])
    assert polar(witness,flip(witness))==-2
    # The eight-dimensional Zorn norm is recovered by y=-V_spatial.
    detz=z[0]*z[1]-sum(z[j]*(-z[j+4]) for j in (3,4,5))
    assert_zero(q(z)-(detz-z[2]*z[6]))
    u=s.Matrix(s.symbols('x0:4',real=True));v=s.Matrix(s.symbols('y0:4',real=True))
    assert wedge(u,u)==s.zeros(6,1)
    assert (wedge(v,u)+wedge(u,v)).applyfunc(s.expand)==s.zeros(6,1)
    H=s.zeros(6)
    for j in range(3): H[j,j+3]=1;H[j+3,j]=-1
    P=s.diag(-1,-1,-1,1,1,1)
    P4=s.diag(1,-1,-1,-1)
    assert H*H==-s.eye(6)
    assert H*P==-P*H
    assert (wedge(P4*u,P4*v)-P*wedge(u,v)).applyfunc(s.expand)==s.zeros(6,1)
    plus=(s.eye(6)-s.I*H)/2;minus=(s.eye(6)+s.I*H)/2
    assert plus*P==P*minus and minus*P==P*plus
    # Exact 5-mode exterior creation/contraction realization: 32 states, no truncation beyond Fock.
    creations=[];annihilations=[]
    for i in range(5):
        C=s.zeros(32);A=s.zeros(32)
        for mask in range(32):
            sign=(-1)**((mask&((1<<i)-1)).bit_count())
            if mask&(1<<i): A[mask^(1<<i),mask]=sign
            else: C[mask|(1<<i),mask]=sign
        creations.append(C);annihilations.append(A)
    for i in range(5):
        for j in range(5):
            assert creations[i]*annihilations[j]+annihilations[j]*creations[i]==(s.eye(32) if i==j else s.zeros(32))
    coeff=list(coordinates(z));p=coeff[:5];n=coeff[5:]
    action=s.zeros(32)
    for i in range(5): action += (p[i]+n[i])*creations[i]+(p[i]-n[i])*annihilations[i]
    assert (action*action-q(z)*s.eye(32)).applyfunc(s.expand)==s.zeros(32)
    out={'diagonalization':True,'inverse_both_directions':True,'swap_matrix_determinant':-1,
         'source_involutions_preserve_q':True,'fundamental_polar_equals_ten_squares':True,
         'source_sign_flip_negative_witness':-2,'native_Zorn_norm_plus_hyperbolic_plane':True,
         'native_wedge_coordinate_identities':True,'Lorentz_Hodge_square':-1,
         'orientation_reversal_swaps_chiral_projections':True,'five_mode_mixed_CAR_cases':25,
         'exact_32_by_32_exterior_action_square':True,
         'Lean_kernel_executed':False,'scope':'Exact symbolic/matrix regression, not Lean elaboration'}
    folder=ROOT/'reports/polarized_boundary55';folder.mkdir(parents=True,exist_ok=True)
    (folder/'exact-regressions.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__': main()
