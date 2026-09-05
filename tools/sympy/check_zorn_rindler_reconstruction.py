#!/usr/bin/env python3
"""Exact symbolic regressions. These do not elaborate or kernel-check Lean."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s

ROOT = Path(__file__).resolve().parents[2]
checks: list[dict[str, str]] = []

def check(name: str, expr) -> None:
    entries = list(expr) if isinstance(expr, (s.MatrixBase, list, tuple)) else [expr]
    residuals = [s.simplify(s.expand(x)) for x in entries]
    if any(x != 0 for x in residuals):
        raise AssertionError(f"{name}: {residuals}")
    checks.append({"name": name, "status": "passed"})

def zmul(X, Y, source=False):
    a, b = X[0], X[7]; c, d = Y[0], Y[7]
    u, v = s.Matrix(X[1:4]), s.Matrix(X[4:7])
    w, z = s.Matrix(Y[1:4]), s.Matrix(Y[4:7])
    sign = 1 if source else -1
    return s.Matrix([a*c+u.dot(z), *(a*w+d*u+sign*v.cross(z)),
                     *(c*v+b*z-sign*u.cross(w)), b*d+v.dot(w)])

def orient(X):
    return s.Matrix([X[0], *[-x for x in X[1:7]], X[7]])

def znorm(X):
    return X[0]*X[7]-s.Matrix(X[1:4]).dot(s.Matrix(X[4:7]))

one = s.Matrix([1, 0, 0, 0, 0, 0, 0, 1])
plus = s.Matrix([1, 0, 0, 0, 0, 0, 0, 0]); minus = one-plus
basis = [s.eye(8)[:, j] for j in range(8)]
X = s.Matrix(s.symbols('x0:8', real=True)); Y=s.Matrix(s.symbols('y0:8', real=True))
u=s.Matrix(s.symbols('u0:3', real=True)); v=s.Matrix(s.symbols('v0:3', real=True))

def create(u): return s.Matrix([0, *(-u), 0, 0, 0, 0])
def lower(u): return s.Matrix([0, 0, 0, 0, *(-u), 0])
def gamma(u): return create(u)-lower(u)
def kappa(u): return create(u)+lower(u)
def left(X): return s.Matrix.hstack(*(zmul(X, y) for y in basis))

def quaternion(q): return s.Matrix([q[0], -q[1], -q[2], -q[3], q[1], q[2], q[3], q[0]])
def qmul(p,q):
    pv,qv=s.Matrix(p[1:]),s.Matrix(q[1:])
    return [p[0]*q[0]-pv.dot(qv), *(p[0]*qv+q[0]*pv+pv.cross(qv))]

check('orientation intertwines the two sign conventions', orient(zmul(X,Y,True))-zmul(orient(X),orient(Y)))
check('orientation preserves split norm', znorm(orient(X))-znorm(X))
check('left unit', zmul(one,X)-X); check('right unit', zmul(X,one)-X)
check('poles are complementary', plus+minus-one)
check('upper pole idempotent',zmul(plus,plus)-plus)
check('lower pole idempotent',zmul(minus,minus)-minus)
check('pole orthogonality both orders',list(zmul(plus,minus))+list(zmul(minus,plus)))
check('gamma square', zmul(gamma(u),gamma(u))+u.dot(u)*one)
check('kappa square', zmul(kappa(u),kappa(u))-u.dot(u)*one)
check('quaternion vector product',zmul(gamma(u),gamma(v))+u.dot(v)*one-gamma(u.cross(v)))
p=s.symbols('p0:4',real=True);q=s.symbols('q0:4',real=True)
check('full quaternion multiplication embedding',zmul(quaternion(p),quaternion(q))-quaternion(qmul(p,q)))
check('creation square',zmul(create(u),create(u)))
check('annihilation square',zmul(lower(u),lower(u)))
check('mixed product upper',zmul(create(u),lower(v))-u.dot(v)*plus)
check('mixed product lower',zmul(lower(v),create(u))-u.dot(v)*minus)
check('creation creation cross term',zmul(create(u),create(v))+lower(u.cross(v)))
check('annihilation annihilation cross term',zmul(lower(u),lower(v))-create(u.cross(v)))
check('left alternativity on full eight-coordinate module',left(X)*left(X)-left(zmul(X,X)))
check('polarized left alternativity',left(X)*left(Y)+left(Y)*left(X)-left(zmul(X,Y)+zmul(Y,X)))
R,L=left(create(u)),left(lower(u));Rv,Lv=left(create(v)),left(lower(v))
check('operator same-raising CAR',R*Rv+Rv*R)
check('operator same-lowering CAR',L*Lv+Lv*L)
check('operator mixed CAR',R*Lv+Lv*R-u.dot(v)*s.eye(8))
check('positive coefficient adjoint',R.T-L)
check('number operator scaled idempotence',(R*L)**2-u.dot(u)*(R*L))
check('Cl(3,3) vector square',left(gamma(u)+kappa(v))**2-(v.dot(v)-u.dot(u))*s.eye(8))

# Show, rather than suppress, the nonassociative obstruction.
e0,e1,e2=[s.eye(3)[:,i] for i in range(3)]
if left(gamma(e0))*left(gamma(e1)) == left(gamma(e2)):
    raise AssertionError('Missing expected quaternion operator obstruction')
checks.append({'name':'quaternion element product is not full-module operator product','status':'passed'})

# Coordinate calculus and two-band spectrum.
a,x,t,dt,dx=s.symbols('a x t dt dx',real=True,nonzero=True)
N=1+a*x; r=x+1/a;acc=a/N
check('log lapse gradient',s.diff(s.log(N),x)-acc)
check('stationary acceleration gradient',s.diff(acc,x)+acc**2)
T=r*s.sinh(a*t);Z=r*s.cosh(a*t)
check('time Jacobian',s.diff(T,t)-N*s.cosh(a*t))
check('space Jacobian',s.diff(Z,t)-N*s.sinh(a*t))
jac=s.Matrix([[s.diff(T,t),s.diff(T,x)],[s.diff(Z,t),s.diff(Z,x)]])
check('Minkowski metric pullback',jac.T*s.diag(-1,1)*jac-s.diag(-N**2,1))
check('coordinate Jacobian determinant',jac.det()-N)
J=s.Matrix([[0,1],[1,0]]);eta=s.diag(-1,1)
check('Lorentz skew connection',(a*J).T*eta+eta*(a*J))
check('Cartan torsion coefficient',-s.diff(N,x)+a)
check('constant one-direction connection curvature',s.diff(a*J,x))
T0,c,eps,rho,c0,c1=s.symbols('T0 c eps rho c0 c1',real=True,nonzero=True)
check('Tolman product',(T0/N)*N-T0)
check('Euclidean angle normalization',a*(2*s.pi/a)-2*s.pi)
check('modular rapidity normalization',2*s.pi*(a*t/(2*s.pi))-a*t)
phi=c0+c1*x-rho*x*x/(2*eps);E=-s.diff(phi,x)
check('uniform-charge Gauss law',eps*s.diff(E,x)-rho)
check('uniform-charge Poisson equation',s.diff(phi,x,2)+rho/eps)
Elog=-c*acc
check('log-lapse electrostatic source',eps*s.diff(Elog,x)-eps*c*acc**2)

b,m,dr,di,energy=s.symbols('b m dr di energy',real=True)
d=dr+s.I*di;H=s.Matrix([[b+m,d],[s.conjugate(d),b-m]]);H0=H-b*s.eye(2)
g=m*m+dr*dr+di*di
check('Hermiticity',H.H-H)
check('centred matrix square',H0**2-g*s.eye(2))
check('characteristic determinant',(H-energy*s.eye(2)).det()-((b-energy)**2-g))
check('positive characteristic root',(H-(b+s.sqrt(g))*s.eye(2)).det())
check('negative characteristic root',(H-(b-s.sqrt(g))*s.eye(2)).det())
check('shift-independent band gap',(b+s.sqrt(g))-(b-s.sqrt(g))-2*s.sqrt(g))
check('particle-hole obstruction',J*s.conjugate(H)*J+H-s.Matrix([[2*b,2*d],[2*s.conjugate(d),2*b]]))
ni,e,z=s.symbols('ni e z',real=True)
n=ni*s.exp(z);p=ni*s.exp(-z)
check('Boltzmann mass action',n*p-ni*ni)
check('charge sign identity',s.expand((e*(p-n)+2*e*ni*s.sinh(z)).rewrite(s.exp)))
check('charge differential',s.expand((s.diff(e*(p-n),z)+2*e*ni*s.cosh(z)).rewrite(s.exp)))

report={'evidence':'exact SymPy identities; NOT Lean elaboration or kernel verification',
        'sympy_version':s.__version__,'check_count':len(checks),'checks':checks}
out=ROOT/'reports/zorn-rindler-symbolic-checks.json';out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(report,indent=2)+'\n')
print(f'{len(checks)} exact symbolic checks passed. Lean verification remains separate.')
