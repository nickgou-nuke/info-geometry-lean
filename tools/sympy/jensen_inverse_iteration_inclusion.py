#!/usr/bin/env python3
"""Finite witness for Jensen inverse-iteration inclusion acceleration.

This checks the algebraic part formalized in
`lean/InfoGeometry/Canonical/JensenInverseIterationInclusion.lean`: Jensen's
quadratic polynomial, its smaller-root formula, and the interval readout
`|λ-μ| ≤ δ_j => λ ∈ [μ-δ_j, μ+δ_j]`.
"""

import sympy as sp


def jensen_polynomial(b, j, z):
    return (-(b[j - 1] - b[j]) * z**2
            + b[j - 1] * (b[j - 2] - b[j]) * z
            - b[j - 1] * b[j] * (b[j - 2] - b[j - 1]))


def accelerated_radius_formula(b, j):
    radicand = ((b[j - 2] - b[j])**2
                - 4 * (b[j - 1] - b[j]) * (b[j - 2] - b[j - 1]) * (b[j] / b[j - 1]))
    return b[j - 1] * ((b[j - 2] - b[j]) - sp.sqrt(radicand)) / (2 * (b[j - 1] - b[j]))


def main():
    # A monotone convergent positive sequence modeling Jensen's c_j/b_j layer.
    h = sp.Rational(1, 5)
    q = sp.Rational(1, 3)
    b = {j: h + q**j for j in range(1, 8)}

    for j in range(3, 8):
        delta = sp.simplify(accelerated_radius_formula(b, j))
        poly_at_delta = sp.simplify(jensen_polynomial(b, j, delta))
        if poly_at_delta != 0:
            raise AssertionError(f"stage {j}: polynomial root check failed: {poly_at_delta}")
        if not (sp.N(h) <= sp.N(delta) <= sp.N(b[j])):
            raise AssertionError(f"stage {j}: expected h <= delta <= b_j, got {delta}, {b[j]}")

        # Interval readout for target eigenvalue lambda = mu + h.
        mu = sp.Rational(7, 2)
        lam = mu + h
        if not (sp.N(mu - delta) <= sp.N(lam) <= sp.N(mu + delta)):
            raise AssertionError(f"stage {j}: target not in accelerated interval")

    print("jensen inverse-iteration inclusion witness: ok")


if __name__ == "__main__":
    main()
