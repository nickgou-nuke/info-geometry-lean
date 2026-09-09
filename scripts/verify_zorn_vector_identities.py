"""Exact finite CAS certificate for the reusable Zorn vector identities.

The carrier alignment is the Lean owner
``InfoGeometry.Exceptional.RealZorn.Vec3Real`` with coordinate order
``(x, y, z)``.  This script is discovery/certificate data only; the Lean
theorems in ``SplitOctonionZornReal.lean`` reconstruct the identities.
"""

import sympy as sp


def vec(prefix):
    return sp.Matrix(sp.symbols(f"{prefix}1:{prefix}4"))


def dot(u, v):
    return (u.T * v)[0]


def cross(u, v):
    return u.cross(v)


def check_vector(name, lhs, rhs):
    residual = [sp.expand(x) for x in lhs - rhs]
    assert all(x == 0 for x in residual), (name, residual)
    print(f"{name}: PASS")


u, v, w = vec("u"), vec("v"), vec("w")
c = sp.symbols("c")

check_vector("dot_cross_left", sp.Matrix([dot(u, cross(v, w))]),
             sp.Matrix([dot(v, cross(w, u))]))
check_vector("dot_cross_right", sp.Matrix([dot(cross(u, v), w)]),
             sp.Matrix([dot(u, cross(v, w))]))
check_vector("cross_cross", cross(cross(u, v), w),
             v * dot(u, w) - u * dot(v, w))
check_vector("cross_add_left", cross(u + v, w),
             cross(u, w) + cross(v, w))
check_vector("cross_add_right", cross(u, v + w),
             cross(u, v) + cross(u, w))
check_vector("cross_smul_left", cross(c * u, v), c * cross(u, v))
check_vector("cross_smul_right", cross(u, c * v), c * cross(u, v))
check_vector("dot_add_left", sp.Matrix([dot(u + v, w)]),
             sp.Matrix([dot(u, w) + dot(v, w)]))
check_vector("dot_add_right", sp.Matrix([dot(u, v + w)]),
             sp.Matrix([dot(u, v) + dot(u, w)]))
check_vector("dot_smul_left", sp.Matrix([dot(c * u, v)]),
             sp.Matrix([c * dot(u, v)]))
check_vector("dot_smul_right", sp.Matrix([dot(u, c * v)]),
             sp.Matrix([c * dot(u, v)]))

print("ZORN_VECTOR_CERTIFICATE=PASS")
