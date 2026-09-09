#!/usr/bin/env python3
"""CAS regression mirror for normalized spherical vMF Bessel formulas.

This script is not a proof dependency. Lean's integral/Esscher construction remains
the theorem owner. The calculations guard the normalization and derivative formulas
that a future general-order modified-Bessel Lean development must prove.
"""

from __future__ import annotations

import sympy as sp


def normalized_partition(dimension: int, kappa: sp.Symbol) -> sp.Expr:
    """Probability-normalized spherical vMF partition for kappa > 0."""
    half_dimension = sp.Rational(dimension, 2)
    nu = half_dimension - 1
    return (
        sp.gamma(half_dimension)
        * (sp.Rational(2, 1) / kappa) ** nu
        * sp.besseli(nu, kappa)
    )


def main() -> None:
    kappa = sp.symbols("kappa", positive=True)

    for dimension in range(2, 9):
        nu = sp.Rational(dimension, 2) - 1
        partition = normalized_partition(dimension, kappa)

        at_zero = sp.simplify(sp.limit(partition, kappa, 0, dir="+"))
        assert at_zero == 1, (dimension, at_zero)

        log_derivative = sp.simplify(sp.diff(sp.log(partition), kappa))
        bessel_ratio = sp.besseli(nu + 1, kappa) / sp.besseli(nu, kappa)
        residual = sp.simplify(log_derivative - bessel_ratio)
        assert residual == 0, (dimension, residual)

    print(
        "Verified dimensions 2..8: normalized Z_d(0)=1 and "
        "d/dkappa log Z_d = I_{nu+1}/I_nu."
    )


if __name__ == "__main__":
    main()
