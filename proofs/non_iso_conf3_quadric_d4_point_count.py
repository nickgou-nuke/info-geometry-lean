#!/usr/bin/env python3
"""Finite-field point-count fingerprint for the D=4 non-isotropic 3-point space.

After translation, the space is

  U_4 = {(a,b) in F_p^4 x F_p^4 | q(a) q(b) q(a-b) != 0}

for q(z)=z0^2+z1^2+z2^2+z3^2.

The script counts U_4(F_p) using a 4D cyclic convolution and verifies the
interpolated polynomial

  p^2 (p-1)^2 (p+1) (p^3 - 2p^2 - p + 3).

This is evidence for the compactly supported/E-polynomial shape, not by itself
a proof of the complex cohomology ring.
"""

from __future__ import annotations

import numpy as np
import sympy as sp


def count_u4_fp(p: int) -> int:
    shape = (p, p, p, p)
    noniso = np.zeros(shape, dtype=float)
    isotropic = np.zeros(shape, dtype=float)

    for z0 in range(p):
        z0sq = z0 * z0
        for z1 in range(p):
            z01 = (z0sq + z1 * z1) % p
            for z2 in range(p):
                z012 = (z01 + z2 * z2) % p
                for z3 in range(p):
                    q = (z012 + z3 * z3) % p
                    if q:
                        noniso[z0, z1, z2, z3] = 1.0
                    else:
                        isotropic[z0, z1, z2, z3] = 1.0

    # C[c] = #{a | q(a) != 0 and q(a-c) != 0}; q is even, so convolution works.
    fourier = np.fft.fftn(noniso)
    convolution = np.fft.ifftn(fourier * fourier).real
    bad_difference = round(float((convolution * isotropic).sum()))
    total_noniso_pairs = int(noniso.sum()) ** 2
    return total_noniso_pairs - bad_difference


def count_polynomial(p: int) -> int:
    return p**2 * (p - 1) ** 2 * (p + 1) * (p**3 - 2 * p**2 - p + 3)


def isotropic_vector_count(p: int) -> int:
    return p * (p**2 + p - 1)


def nonisotropic_vector_count(p: int) -> int:
    return p * (p - 1) ** 2 * (p + 1)


def bad_difference_count(p: int) -> int:
    return p**2 * (p - 1) ** 2 * (p + 1) * (p**2 - 2)


def main() -> None:
    primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    points = []
    for p in primes:
        count = count_u4_fp(p)
        expected = count_polynomial(p)
        assert count == expected
        assert p**4 - isotropic_vector_count(p) == nonisotropic_vector_count(p)
        assert nonisotropic_vector_count(p) ** 2 - bad_difference_count(p) == expected
        points.append((p, count))

    x = sp.symbols("x")
    interpolated = sp.interpolate(points[:9], x)
    expected_poly = x**2 * (x - 1) ** 2 * (x + 1) * (x**3 - 2 * x**2 - x + 3)
    assert sp.expand(interpolated - expected_poly) == 0

    print("non_iso_conf3_quadric_d4_point_count.py: point-count fingerprint passed")
    print("#U_4(F_p) =")
    sp.pprint(sp.factor(expected_poly))
    print("lemma chain:")
    print("  Z(p)=#isotropic vectors =", "p*(p**2+p-1)")
    print("  S(p)=#non-isotropic vectors =", "p*(p-1)**2*(p+1)")
    print("  bad(p)=#bad differences =", "p**2*(p-1)**2*(p+1)*(p**2-2)")
    for p, count in points:
        print(f"p={p:2d}: {count}")
    print("Interpretation remains conditional: polynomial count is not yet a cohomology-ring proof.")


if __name__ == "__main__":
    main()
