#!/usr/bin/env sage
from sage.all import QQ, vector

x = vector(QQ, [1, 2, 3, 4, 5, -1, -2, -3, -4, -5])

def neg_all(v):
    return -v

def refl_pair0(v):
    out = vector(QQ, v)
    out[0] = -out[0]
    out[5] = -out[5]
    return out

def refl_pair1(v):
    out = vector(QQ, v)
    out[1] = -out[1]
    out[6] = -out[6]
    return out

def refl_pair01(v):
    return refl_pair0(refl_pair1(v))

def projective_sign_eq(a, b):
    return b == a or b == neg_all(a)

def in_v4_orbit(a, b):
    return b == a or b == refl_pair0(a) or b == refl_pair1(a) or b == refl_pair01(a)

orbit = [x, refl_pair0(x), refl_pair1(x), refl_pair01(x)]

for y in orbit:
    assert in_v4_orbit(x, y)
    assert in_v4_orbit(x, refl_pair0(y))
    assert in_v4_orbit(x, refl_pair1(y))
    assert in_v4_orbit(neg_all(x), neg_all(y))

for y in orbit:
    for z in orbit:
        if projective_sign_eq(y, z):
            assert projective_sign_eq(refl_pair0(y), refl_pair0(z))
            assert projective_sign_eq(refl_pair1(y), refl_pair1(z))
            assert projective_sign_eq(refl_pair01(y), refl_pair01(z))
            assert projective_sign_eq(neg_all(y), neg_all(z))

print("SAGE_O55_PROJECTIVE_DESCENT_OK")
print("SAGE_O55_V4_ORBIT_CLOSED_OK")
print("SAGE_O55_NEGALL_ORBIT_CLOSED_OK")
