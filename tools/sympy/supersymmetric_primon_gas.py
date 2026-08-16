#!/usr/bin/env python3
"""Finite witness for the supersymmetric primon gas algebra.

This mirrors `InfoGeometry.Arithmetic.SupersymmetricPrimonGas`.

Verified finite layers:

* bosonic Euler factor product: prod_p (1 - x_p)^-1;
* ordinary fermionic product: prod_p (1 + x_p);
* signed Witten/Mobius product: prod_p (1 - x_p);
* second-order correction: prod_p (1 - x_p^2);
* finite identities behind `1/zeta(s)` and `zeta(s)/zeta(2s)`;
* Mobius parity on squarefree states and zero on repeated-prime sectors;
* tripotent `{+1,-1,0}` projectors for boson/fermion/ghost sectors;
* a conditional matrix socket for `Q^2 = H`.

No infinite Euler product, C*-completion, spectral mass-gap theorem, or RH
claim is verified here.
"""

import sys
from itertools import combinations
from math import prod
from pathlib import Path

import sympy as sp

_REPO_ROOT = Path(__file__).resolve().parents[2]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sympy.common import assert_matrix_eq


def subsets(xs: list[int]) -> list[tuple[int, ...]]:
    return [tuple(c) for r in range(len(xs) + 1) for c in combinations(xs, r)]


def is_squarefree(n: int) -> bool:
    return sp.mobius(n) != 0


def main() -> None:
    primes = [2, 3, 5, 7]
    beta = 2
    x = {p: sp.Rational(1, p) ** beta for p in primes}

    z_boson = prod(1 / (1 - x[p]) for p in primes)
    z_fermion = prod(1 + x[p] for p in primes)
    z_signed_witten = prod(1 - x[p] for p in primes)
    z_second_order = prod(1 - x[p] ** 2 for p in primes)

    assert sp.simplify(z_boson * z_signed_witten - 1) == 0
    assert sp.simplify(z_fermion * z_signed_witten - z_second_order) == 0
    assert sp.simplify(z_boson * z_second_order - z_fermion) == 0

    # Witten/Mobius supertrace over finite squarefree occupations.
    witten_coeff_sum = 0
    for support in subsets(primes):
        n = prod(support) if support else 1
        parity = (-1) ** len(support)
        assert sp.mobius(n) == parity
        witten_coeff_sum += parity
    assert witten_coeff_sum == 0

    # Repeated-prime sectors collapse under the Mobius/Witten grading.
    for n in [4, 8, 9, 12, 18, 20, 45]:
        assert not is_squarefree(n)
        assert sp.mobius(n) == 0

    # Trifactor sector projectors: T has eigenvalues +1, -1, 0.
    T = sp.diag(1, -1, 0)
    I3 = sp.eye(3)
    Z3 = sp.zeros(3)
    P_boson = (T**2 + T) / 2
    P_fermion = (T**2 - T) / 2
    P_ghost = I3 - T**2
    assert_matrix_eq(T**3, T, "tripotent T^3=T")
    assert_matrix_eq(P_boson**2, P_boson, "boson projector")
    assert_matrix_eq(P_fermion**2, P_fermion, "fermion projector")
    assert_matrix_eq(P_ghost**2, P_ghost, "ghost projector")
    assert_matrix_eq(P_boson * P_fermion, Z3, "boson/fermion orthogonal")
    assert_matrix_eq(P_ghost * P_boson, Z3, "ghost/boson orthogonal")
    assert_matrix_eq(P_ghost * P_fermion, Z3, "ghost/fermion orthogonal")
    assert_matrix_eq(P_ghost + P_boson + P_fermion, I3, "trifactor partition")
    assert_matrix_eq(T * P_boson, P_boson, "T on +1 sector")
    assert_matrix_eq(T * P_fermion, -P_fermion, "T on -1 sector")
    assert_matrix_eq(T * P_ghost, Z3, "T on 0 sector")

    # Conditional supercharge socket: here we choose a concrete Q and define H=Q^2.
    Q = sp.Matrix([[0, 1], [1, 0]])
    H = Q**2
    assert_matrix_eq(Q**2, H, "supercharge square Q^2=H")
    assert_matrix_eq(Q * H, H * Q, "supercharge conservation QH=HQ")
    assert_matrix_eq(H, sp.eye(2), "chosen finite Hamiltonian")

    print("supersymmetric_primon_gas: ok")
    print("  boson/signed: Z_boson * Z_signed_Witten = 1")
    print("  fermion factor: Z_fermion * Z_signed_Witten = Z_second_order")
    print("  zeta-ratio shadow: Z_boson * Z_second_order = Z_fermion")
    print("  Mobius grading: squarefree parity, repeated-prime sectors -> 0")
    print("  trifactor: +1 boson, -1 fermion, 0 ghost projectors resolve identity")
    print("  supercharge socket: Q^2=H and QH=HQ after supplying Q")


if __name__ == "__main__":
    main()
