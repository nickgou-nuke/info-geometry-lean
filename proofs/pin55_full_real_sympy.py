#!/usr/bin/env python3
"""Exact certificate for the real Cl(5,5) reflection generators.

This is a finite matrix certificate, not a replacement for the Lean proof.
It checks a faithful 32x32 real gamma representation, the ten coordinate
reflections, preservation of eta(5,5), and the central +/- identity kernel on
the signed Clifford monomial subgroup.
"""

from itertools import combinations
from sympy import Matrix, eye, diag, kronecker_product, zeros

I2 = eye(2)
X = Matrix([[0, 1], [1, 0]])       # X^2 = +1
Y = Matrix([[0, 1], [-1, 0]])      # Y^2 = -1
Z = diag(1, -1)                    # Jordan-Wigner string


def kron_all(parts):
    out = Matrix([[1]])
    for part in parts:
        out = kronecker_product(out, part)
    return out


def gamma(local, i):
    return kron_all([Z] * i + [local] + [I2] * (4 - i))


gammas = [gamma(X, i) for i in range(5)] + [gamma(Y, i) for i in range(5)]
signs = [1] * 5 + [-1] * 5
I32 = eye(32)
eta = diag(*signs)

# Clifford relations gamma_a gamma_b + gamma_b gamma_a = 2 eta_ab.
for a in range(10):
    for b in range(10):
        expected = 2 * signs[a] * I32 if a == b else zeros(32)
        assert gammas[a] * gammas[b] + gammas[b] * gammas[a] == expected


def twisted_reflection(a):
    """Matrix on V induced by -gamma_a v gamma_a^{-1}."""
    ga = gammas[a]
    ga_inv = signs[a] * ga
    cols = []
    for b in range(10):
        image = -ga * gammas[b] * ga_inv
        coeffs = []
        for c in range(10):
            # trace(gamma_c image)/(32*sign_c) extracts the vector coefficient.
            coeffs.append((gammas[c] * image).trace() / (32 * signs[c]))
        assert image == sum((coeffs[c] * gammas[c] for c in range(10)), zeros(32))
        cols.append(Matrix(coeffs))
    return Matrix.hstack(*cols)


reflections = [twisted_reflection(a) for a in range(10)]
for a, r in enumerate(reflections):
    expected = eye(10)
    expected[a, a] = -1
    assert r == expected
    assert r.T * eta * r == eta
    assert r.det() == -1

# Signed basis monomials are all distinct up to the explicit central sign.
monomials = {}
for degree in range(11):
    for subset in combinations(range(10), degree):
        value = I32
        for a in subset:
            value = value * gammas[a]
        key = tuple(value)
        assert key not in monomials
        monomials[key] = subset
assert len(monomials) == 2**10
assert tuple(I32) in monomials and tuple(-I32) not in monomials

# On the signed Clifford-monomial subgroup, the twisted action is the
# product of the corresponding coordinate reflections.  The two scalar
# signs have the same image, and no nonempty subset acts trivially.
image_keys = set()
kernel_count = 0
for subset in monomials.values():
    image = eye(10)
    for a in subset:
        image = image * reflections[a]
    image_keys.add(tuple(image))
    if image == eye(10):
        kernel_count += 2  # the two central scalar signs
assert len(image_keys) == 2**10
assert kernel_count == 2

print("pin55_full_real_sympy: PASS")
print("real gamma matrix size: 32")
print("Clifford basis rank:", len(monomials))
print("coordinate reflections: 10")
print("reflection determinants:", sorted({r.det() for r in reflections}))
print("metric signature: (5,5)")
print("signed monomial image order:", len(image_keys))
print("signed monomial kernel order:", kernel_count)
