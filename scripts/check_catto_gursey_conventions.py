#!/usr/bin/env python3
"""Exact signed-basis check, not a Lean proof.
Owner: InfoGeometry.Algebra.ZornVectorMatrix.mul (a, upper[3], lower[3], b).
Basis: E22, E11, V0,V1,V2,-U0,-U1,-U2; standard right-handed cross product.
No anti-homomorphism: products are left-to-right. Integer coefficients.
Run this script to reproduce the deterministic JSON convention receipt.
"""
import json


def cross(x, y):
    return [x[1]*y[2]-x[2]*y[1], x[2]*y[0]-x[0]*y[2], x[0]*y[1]-x[1]*y[0]]


def mul(x, y):
    a, u, v, b = x[0], x[1:4], x[4:7], x[7]
    c, z, w, d = y[0], y[1:4], y[4:7], y[7]
    return [a*c+sum(i*j for i,j in zip(u,w)),
            *[a*z[i]+d*u[i]-cross(v,w)[i] for i in range(3)],
            *[c*v[i]+b*w[i]+cross(u,z)[i] for i in range(3)],
            sum(i*j for i,j in zip(v,z))+b*d]


def add(x, y): return [a+b for a,b in zip(x,y)]
def neg(x): return [-a for a in x]
def sub(x,y): return add(x,neg(y))
def comm(x,y): return sub(mul(x,y),mul(y,x))
def scale(c,x): return [c*a for a in x]
def unit(i): return [int(j==i) for j in range(8)]

p,q=unit(7),unit(0)
u=[unit(4+i) for i in range(3)]
v=[neg(unit(1+i)) for i in range(3)]
g=sub(p,q)
one=add(p,q)
for i in range(3):
    for j in range(3):
        assert add(mul(u[i],u[j]),mul(u[j],u[i])) == [0]*8
        assert add(mul(v[i],v[j]),mul(v[j],v[i])) == [0]*8
        assert add(mul(u[i],v[j]),mul(v[j],u[i])) == scale(-int(i==j),one)
for i,j,k in [(0,1,2),(1,2,0),(2,0,1)]:
    assert mul(u[i],u[j]) == v[k]
    assert mul(v[i],v[j]) == u[k]
assert mul(mul(u[0],u[1]),u[2]) == neg(q)
assert mul(u[0],mul(u[1],u[2])) == neg(p)
assert sub(mul(mul(u[0],u[1]),u[2]),mul(u[0],mul(u[1],u[2]))) == g
assert add(add(comm(u[0],comm(u[1],u[2])),comm(u[1],comm(u[2],u[0]))),
           comm(u[2],comm(u[0],u[1]))) == scale(-6,g)
# All 64 structure constants for the bilinear multiplication transport.
# General-ring transport is proved separately in Lean.
def coordinates(a,b,x,y): return [b,*[-v for v in y],*x,a]
for I in range(8):
    for J in range(8):
        X,Y=unit(I),unit(J)
        a,b,x,y=X[0],X[1],X[2:5],X[5:8]
        c,d,z,t=Y[0],Y[1],Y[2:5],Y[5:8]
        expected=coordinates(a*c-sum(x[i]*t[i] for i in range(3)),
                             b*d-sum(y[i]*z[i] for i in range(3)),
                             [a*z[i]+d*x[i]+cross(y,t)[i] for i in range(3)],
                             [c*y[i]+b*t[i]+cross(x,z)[i] for i in range(3)])
        assert mul(coordinates(a,b,x,y),coordinates(c,d,z,t)) == expected
print(json.dumps({'owner':'InfoGeometry.Algebra.ZornVectorMatrix.mul',
    'coordinates':['a','upper0','upper1','upper2','lower0','lower1','lower2','b'],
    'basis':['E22','E11','V0','V1','V2','-U0','-U1','-U2'],
    'anti_hom':False,'basis_relations':'PASS','bilinear_product_transport_64_cells':'PASS',
    'jacobiator_coefficient':-6},sort_keys=True,indent=2))
