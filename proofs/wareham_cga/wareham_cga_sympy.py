#!/usr/bin/env python3
import sympy as sp

x1,x2,x3,y1,y2,y3,a1,a2,a3,lam=sp.symbols('x1 x2 x3 y1 y2 y3 a1 a2 a3 lam')
G=sp.Matrix([[1,0,0,0,0],[0,1,0,0,0],[0,0,1,0,0],[0,0,0,0,-2],[0,0,0,-2,0]])

def dot(u,v):
    return sp.expand((u.T*G*v)[0])

def E(x,y,z):
    q=x*x+y*y+z*z
    return sp.Matrix([x,y,z,sp.Rational(1,2)*q,sp.Rational(1,2)])

def V(x,y,z):
    return sp.Matrix([x,y,z,0,0])

def T_action_on_F(x,y,z,a,b,c):
    return E(x+a,y+b,z+c)

n=sp.Matrix([0,0,0,1,0])
nb=sp.Matrix([0,0,0,0,1])
X=E(x1,x2,x3)
Y=E(y1,y2,y3)
A=V(a1,a2,a3)
checks={
    'n_null': dot(n,n),
    'nb_null': dot(nb,nb),
    'n_nb': dot(n,nb)+2,
    'F_null': dot(X,X),
    'F_distance': dot(X,Y)+sp.Rational(1,2)*((x1-y1)**2+(x2-y2)**2+(x3-y3)**2),
    'translator_target_null': dot(T_action_on_F(x1,x2,x3,a1,a2,a3),T_action_on_F(x1,x2,x3,a1,a2,a3)),
    'dilator_null': dot(E(lam*x1,lam*x2,lam*x3),E(lam*x1,lam*x2,lam*x3)),
}
for k,v in checks.items():
    assert sp.simplify(v)==0,(k,sp.factor(v))
print({k:sp.simplify(v) for k,v in checks.items()})
