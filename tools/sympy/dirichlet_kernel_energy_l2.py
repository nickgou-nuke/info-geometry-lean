#!/usr/bin/env python3
"""
Exact Dirichlet Kernel Energy and Integral Normalization CAS Verification.

Verifies:
1. Cosine integral on [0, 1]: int_0^1 cos(2 pi x) dx = 0.
2. Normalization of Dirichlet kernel: int_0^1 (1 + 2 cos(2 pi x)) dx = 1.
3. L2 energy of D_1(x): int_0^1 (1 + 2 cos(2 pi x))^2 dx = 3.
4. Fourier reproduction: int_0^1 (1 + 2 cos(2 pi x)) cos(2 pi x) dx = 1.
5. General D_N energy scaling: int_0^1 (1 + 2 sum_{k=1}^N cos(2 pi k x))^2 dx = 1 + 2 N.
"""

from __future__ import annotations

import sympy as sp
from igf.cas.assertions import assert_zero


def test_dirichlet_kernel_energy_l2() -> None:
    print("========================================================================")
    print("DIRICHLET KERNEL L2 ENERGY & NORMALIZATION: CAS VERIFICATION")
    print("========================================================================")

    x = sp.symbols("x", real=True)

    # 1. Cosine integral
    cos_int = sp.integrate(sp.cos(2 * sp.pi * x), (x, 0, 1))
    assert_zero(sp.simplify(cos_int), "int_0^1 cos(2 pi x) dx = 0")
    print("  [OK] 1. Exact Cosine Periodic Integral int_0^1 cos(2 pi x) dx = 0 verified")

    # 2. Normalization of D_1(x)
    D1 = 1 + 2 * sp.cos(2 * sp.pi * x)
    D1_int = sp.integrate(D1, (x, 0, 1))
    assert_zero(sp.simplify(D1_int - 1), "int_0^1 D_1(x) dx = 1")
    print("  [OK] 2. Exact Dirichlet Kernel Normalization int_0^1 D_1(x) dx = 1 verified")

    # 3. L2 energy of D_1(x)
    D1_energy = sp.integrate(D1 ** 2, (x, 0, 1))
    assert_zero(sp.simplify(D1_energy - 3), "int_0^1 D_1(x)^2 dx = 3")
    print("  [OK] 3. Exact Dirichlet Kernel L2 Energy int_0^1 D_1(x)^2 dx = 3 verified")

    # 4. Fourier mode reproduction
    D1_reproduce = sp.integrate(D1 * sp.cos(2 * sp.pi * x), (x, 0, 1))
    assert_zero(sp.simplify(D1_reproduce - 1), "int_0^1 D_1(x) cos(2 pi x) dx = 1")
    print("  [OK] 4. Exact Fourier Mode Reproduction int_0^1 D_1(x) cos(2 pi x) dx = 1 verified")

    # 5. Higher order Dirichlet kernel energies N = 1..5
    for N_val in range(1, 6):
        DN = 1 + 2 * sum(sp.cos(2 * sp.pi * k * x) for k in range(1, N_val + 1))
        DN_energy = sp.integrate(DN ** 2, (x, 0, 1))
        expected_energy = 1 + 2 * N_val
        assert_zero(sp.simplify(DN_energy - expected_energy), f"D_{N_val} energy = 1 + 2*{N_val}")
    print("  [OK] 5. Exact Dirichlet Energy Scaling int_0^1 D_N(x)^2 dx = 1 + 2 N verified for N=1..5")

    print("========================================================================")
    print("ALL DIRICHLET KERNEL ENERGY THEOREMS 100% CAS VERIFIED")
    print("========================================================================")


if __name__ == "__main__":
    test_dirichlet_kernel_energy_l2()
