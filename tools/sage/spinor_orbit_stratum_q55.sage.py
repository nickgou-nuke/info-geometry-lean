#!/usr/bin/env sage -python
"""Sage exact witness for q55 zero/null/generic strata."""

from sage.all import QQ, vector


def q55(v):
    return sum(v[i] ** 2 for i in range(5)) - sum(v[i] ** 2 for i in range(5, 10))

zero = vector(QQ, [0] * 10)
e0 = vector(QQ, [1] + [0] * 9)
e5 = vector(QQ, [0] * 5 + [1] + [0] * 4)
null = e0 + e5

assert q55(zero) == 0
assert null != zero and q55(null) == 0
assert q55(e0) == 1
assert q55(e5) == -1
for v in (zero, null, e0, e5):
    assert q55(-v) == q55(v)

print("SAGE_SPINOR_ORBIT_Q55_ZERO_OK")
print("SAGE_SPINOR_ORBIT_Q55_NULL_OK")
print("SAGE_SPINOR_ORBIT_Q55_GENERIC_POS_OK")
print("SAGE_SPINOR_ORBIT_Q55_GENERIC_NEG_OK")
print("SAGE_SPINOR_ORBIT_Q55_NEGALL_PRESERVES_OK")
