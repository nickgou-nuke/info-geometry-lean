#!/usr/bin/env sage
from sage.all import QQ, vector

x = vector(QQ, [0, 0, 3, 4, 5, 0, 0, -3, -4, -5])

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

def in_v4_orbit(a, b):
    return b == a or b == refl_pair0(a) or b == refl_pair1(a) or b == refl_pair01(a)

assert refl_pair0(x) == x
assert refl_pair1(x) == x
assert refl_pair01(x) == x
for y in [x, refl_pair0(x), refl_pair1(x), refl_pair01(x)]:
    assert in_v4_orbit(x, y)
    assert y == x

print("SAGE_O55_STABILIZER_PAIR0_OK")
print("SAGE_O55_STABILIZER_PAIR1_OK")
print("SAGE_O55_STABILIZER_ORBIT_SINGLETON_OK")
