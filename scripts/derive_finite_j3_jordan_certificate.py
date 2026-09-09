#!/usr/bin/env python3
"""Generate exact finite J3/Zorn Jordan certificates.

Discovery only: Lean must reprove the emitted zero identities.  Poly arithmetic
is used instead of expanding Python/SymPy expression trees.
"""
import hashlib
import json
import sympy as sp

N = 3
names = [f"{side}_{i}_{k}_{c}" for side in ("X", "Y")
         for i in range(N) for k in range(N) for c in range(8)]
gens = tuple(sp.Symbol(n) for n in names)
zero = sp.Poly(0, *gens, domain=sp.QQ)

def const(q): return sp.Poly(q, *gens, domain=sp.QQ)
def P(x): return x if isinstance(x, sp.Poly) else const(x)
def add(x, y): return tuple(a + b for a, b in zip(x, y))
def half(x): return tuple(a / 2 for a in x)
def dot(u, v): return u[0]*v[0] + u[1]*v[1] + u[2]*v[2]
def cross(u, v):
    return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2],
            u[0]*v[1]-u[1]*v[0])
def zmul(x, y):
    a,b,*r = x; c,d,*s = y
    u,v = r[:3],r[3:]; w,z = s[:3],s[3:]
    cu = tuple(a*t + d*q - e for t,q,e in zip(w,u,cross(v,z)))
    cv = tuple(c*t + b*q + e for t,q,e in zip(v,z,cross(u,w)))
    return (a*c + dot(u,z), b*d + dot(v,w), *cu, *cv)
def mmul(x, y, i, k):
    return add(add(zmul(x[i][0], y[0][k]), zmul(x[i][1], y[1][k])),
               zmul(x[i][2], y[2][k]))
def jordan(x, y, i, k): return half(add(mmul(x,y,i,k), mmul(y,x,i,k)))
def matrix(side):
    return [[tuple(sp.Poly(sp.Symbol(f"{side}_{i}_{k}_{c}"), *gens, domain=sp.QQ)
                    for c in range(8)) for k in range(N)] for i in range(N)]
def jp(x, y): return [[jordan(x,y,i,k) for k in range(N)] for i in range(N)]
def assoc(x, y):
    xx, yx = jp(x,x), jp(y,x)
    xy = jp(x,y)
    left = jp(xx,yx)
    right = jp(x,jp(xy,x))
    return [[tuple(a-b for a,b in zip(left[i][k], right[i][k]))
             for k in range(N)] for i in range(N)]

result = []
for i, row in enumerate(assoc(matrix("X"), matrix("Y"))):
    for k, entry in enumerate(row):
        polys = [p for p in entry]
        serial = "|".join(str(p.as_expr()) for p in polys)
        result.append({"i": i, "k": k, "components": 8,
                       "zero": all(p == zero for p in polys),
                       "term_counts": [len(p.terms()) for p in polys],
                       "sha256": hashlib.sha256(serial.encode()).hexdigest()})

assert all(r["zero"] for r in result)
print(json.dumps({
    "object": "finite_j3_jordan_associator",
    "lean_owner": "InfoGeometry.Exceptional.RealZorn.FiniteJ3ZornCarrier",
    "carrier": "J3 = Fin 3 -> Fin 3 -> ZornMatrixReal",
    "basis_order": ["a", "b", "u0", "u1", "u2", "v0", "v1", "v2"],
    "matrix_order": "row-major (i,k)",
    "checked_cases": result,
}, sort_keys=True))
