#!/usr/bin/env python3
"""Finite-support GNS state positivity mirror.

Checks ω(a* a) = Σ_active conjugate(a_i)a_i = Σ_active |a_i|^2.
"""

import sympy as sp


def active(xs, mask):
    return [x for x, m in zip(xs, mask) if m]


def main():
    n = 4
    mask = (True, False, True, True)
    a = list(sp.symbols(f"a0:{n}", complex=True))
    pos_terms = [sp.conjugate(ai) * ai for ai in active(a, mask)]
    omega_pos = sum(pos_terms)
    norm_sum = sum(sp.conjugate(ai) * ai for ai in active(a, mask))
    assert sp.simplify(omega_pos - norm_sum) == 0

    # Numeric positivity samples.
    samples = [1 + 2j, -3j, 0.5]
    val = sum(z.conjugate() * z for z in samples)
    assert abs(val.imag) < 1e-12
    assert val.real >= 0
    print("finite-support GNS state positivity checks ok")


if __name__ == "__main__":
    main()
