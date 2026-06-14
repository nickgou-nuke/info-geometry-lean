#!/usr/bin/env sage -python
"""Sage exact matrix witness for finite O(5,5)/sign/V4 shadows.

Verifies finite rational matrix facts only:
1. η = diag(1^5, -1^5) is symmetric;
2. coordinate sign reflections preserve η;
3. two selected reflections generate four distinct commuting involutive matrices;
4. (r_0*r_5)^2 = I;
5. -I preserves η and has order 2;
6. the usual dimension numerology for so(5,5), namely 10*9/2 = 45.

This is not a Lean proof, not a Clifford algebra construction, and not a
construction of O(5,5)/{±I} or Pin(5,5).
"""
from sage.all import QQ, identity_matrix, diagonal_matrix, det, matrix

n = 10
eta = diagonal_matrix(QQ, [1]*5 + [-1]*5)
assert eta == eta.transpose(), "η must be symmetric"

def is_orthogonal(M):
    """Check M^T·η·M = η."""
    return M.transpose() * eta * M == eta

# Basis reflection: negate coordinate i
def reflect(i):
    M = identity_matrix(QQ, n)
    M[i, i] = -1
    return M

# Check reflections
for i in range(10):
    r_i = reflect(i)
    assert is_orthogonal(r_i), f"r_{i} not in O(5,5)"
    assert det(r_i) == -1, f"r_{i} has det != -1"

print(f"SAGE_PIN55_REFLECTIONS_ALL_10_IN_O55: OK")

# Four-element commuting-reflection shadow from coordinates 0 and 5.
r0 = reflect(0)
r5 = reflect(5)
r0r5 = r0 * r5

# V4: (r0*r5)^2 = I
assert (r0r5 * r0r5).is_one()
assert r0r5 != identity_matrix(QQ, n)
assert r0r5 * r0r5 == identity_matrix(QQ, n), "(r0*r5)^2 ≠ I"

# Four distinct matrices; use immutable copies for hashing.
def immutable_copy(M):
    N = matrix(QQ, M)
    N.set_immutable()
    return N

v4_set = {immutable_copy(identity_matrix(QQ, n)), immutable_copy(r0), immutable_copy(r5), immutable_copy(r0r5)}
assert len(v4_set) == 4, "commuting-reflection shadow should have 4 distinct elements"
assert r0 * r5 == r5 * r0
print(f"SAGE_PIN55_V4_SHADOW_ORDER=4")

# Central {I, -I} quotient
negI = -identity_matrix(QQ, n)
assert is_orthogonal(negI), "-I ∉ O(5,5)"
assert negI * negI == identity_matrix(QQ, n)
print(f"SAGE_PIN55_NEGI_IN_O55: OK")
print(f"SAGE_PIN55_NEGI_ORDER=2")

# Dimension numerology for so(5,5): n(n-1)/2 for n=10.
SOr0 = reflect(0) * reflect(1)  # two reflections → determinant 1
assert det(SOr0) == 1
assert is_orthogonal(SOr0)
assert n * (n - 1) // 2 == 45
print(f"SAGE_SO55_DIM_NUMEROLOGY=45")
print(f"SAGE_PSO55_DIM_NUMEROLOGY=45")

# Signature signs matched by the diagonal metric.
print("SAGE_CL55_SIGNATURE_SHADOW: e0..e4 +1 e5..e9 -1")

print(f"SAGE_PIN55_ALL_CHECKED_OK")
