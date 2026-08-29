#!/usr/bin/env python3
"""Exact SymPy certificate for reusable real Zorn vector identities.

Lean reconstruction: Exceptional/SplitOctonionZornReal.lean.
"""
import sympy as s

def V(prefix): return s.symbols(prefix + '0:3')
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def smul(c,a): return tuple(c*x for x in a)
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def cross(a,b): return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def eqv(a,b): return all(s.expand(x-y) == 0 for x,y in zip(a,b))
def check(name, lhs, rhs):
    assert eqv(lhs, rhs), name
    return name

u,v,w = V('u'), V('v'), V('w')
c = s.symbols('c')
checks = [
    check('dot_cross_left', (dot(u,cross(v,w)),), (dot(v,cross(w,u)),)),
    check('dot_cross_right', (dot(cross(u,v),w),), (dot(u,cross(v,w)),)),
    check('cross_cross', cross(cross(u,v),w), add(smul(dot(u,w),v), smul(-dot(v,w),u))),
    check('add_dot_left', (dot(add(u,v),w),), (dot(u,w)+dot(v,w),)),
    check('add_dot_right', (dot(u,add(v,w)),), (dot(u,v)+dot(u,w),)),
    check('smul_dot_left', (dot(smul(c,u),v),), (c*dot(u,v),)),
    check('smul_dot_right', (dot(u,smul(c,v)),), (c*dot(u,v),)),
    check('cross_add_left', cross(add(u,v),w), add(cross(u,w),cross(v,w))),
    check('cross_add_right', cross(u,add(v,w)), add(cross(u,v),cross(u,w))),
    check('cross_smul_left', cross(smul(c,u),v), smul(c,cross(u,v))),
    check('cross_smul_right', cross(u,smul(c,v)), smul(c,cross(u,v))),
]
print('ZORN_VECTOR_CERTIFICATE=PASS')
print('IDENTITIES=' + ','.join(checks))
