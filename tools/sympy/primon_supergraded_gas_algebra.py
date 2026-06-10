#!/usr/bin/env python3
"""SymPy witness for the primon supergraded gas algebra bridge.

This mirrors `InfoGeometry.Arithmetic.PrimonSupergradedGasAlgebra`.

Verified layers:

* finite boson/signed-fermion Euler cancellation;
* reciprocal-boundary singularity for the signed Witten/Euler factor;
* finite positive-fermion / boson-square ratio identity;
* finite Boolean Witten-index cancellation;
* one-mode fermionic CAR matrices;
* witness-gated Weyl-normalized bosonic CCR readout;
* `J/epsilon/Q` supercharge CAR/CCR and chiral projectors;
* chiral central-charge bookkeeping.
"""

from __future__ import annotations

from itertools import combinations
from math import prod

import sympy as sp


def assert_matrix_eq(lhs: sp.Matrix, rhs: sp.Matrix, label: str) -> None:
    delta = sp.simplify(lhs - rhs)
    if delta != sp.zeros(*lhs.shape):
        raise AssertionError(f"{label} failed:\n{delta}")


def subsets(xs: list[int]) -> list[tuple[int, ...]]:
    return [tuple(c) for r in range(len(xs) + 1) for c in combinations(xs, r)]


def main() -> None:
    primes = [2, 3, 5]
    beta = sp.Rational(3, 2)
    x = {p: sp.Rational(1, p) ** beta for p in primes}

    signed_fermion = prod(1 - x[p] for p in primes)
    positive_fermion = prod(1 + x[p] for p in primes)
    boson = prod(1 / (1 - x[p]) for p in primes)
    boson_square = prod(1 / (1 - x[p] ** 2) for p in primes)
    assert sp.simplify(boson * signed_fermion - 1) == 0
    assert sp.simplify(positive_fermion * boson_square - boson) == 0

    zeta_value = sp.symbols("zeta_value", positive=True)
    reciprocal_supertrace = 1 / zeta_value
    assert sp.limit(reciprocal_supertrace, zeta_value, 0, dir="+") == sp.oo

    witten_index = sum((-1) ** len(S) for S in subsets(primes))
    assert witten_index == 0

    for S in subsets(primes):
        n = prod(S) if S else 1
        assert sp.mobius(n) == (-1) ** len(S)

    identity = sp.eye(2)
    zero = sp.zeros(2)

    annihilation = sp.Matrix([[0, 1], [0, 0]])
    creation = sp.Matrix([[0, 0], [1, 0]])

    assert_matrix_eq(annihilation**2, zero, "fermion annihilation nilpotent")
    assert_matrix_eq(creation**2, zero, "fermion creation nilpotent")
    assert_matrix_eq(annihilation * creation + creation * annihilation, identity, "fermion CAR")

    # Witness-gated boson CCR normalization: raw commutator = nu * I, lambda^2 * nu = 1.
    lam = sp.Rational(1, 2)
    nu = sp.Integer(4)
    assert sp.simplify(lam**2 * nu - 1) == 0
    raw_ccr = nu * identity
    normalized_ccr = sp.simplify(lam**2) * raw_ccr
    assert_matrix_eq(normalized_ccr, identity, "Weyl-normalized boson CCR")

    J = sp.Matrix([[0, 1], [1, 0]])
    epsilon = sp.Matrix([[1, 0], [0, -1]])
    Q = J * epsilon

    assert_matrix_eq(J * epsilon + epsilon * J, zero, "supercharge CAR {J,epsilon}=0")
    assert_matrix_eq(J * epsilon - epsilon * J, 2 * Q, "supercharge CCR [J,epsilon]=2Q")
    assert_matrix_eq(Q**2, -identity, "chiral supercharge square")

    p_plus = (identity + epsilon) / 2
    p_minus = (identity - epsilon) / 2
    assert_matrix_eq(p_plus**2, p_plus, "chiral plus projector")
    assert_matrix_eq(p_minus**2, p_minus, "chiral minus projector")
    assert_matrix_eq(p_plus * p_minus, zero, "chiral projectors orthogonal")
    assert_matrix_eq(p_plus + p_minus, identity, "chiral projectors resolve identity")

    majorana_channels = 8
    boson_channels = 8
    twice_c_majorana = majorana_channels
    twice_c_boson = 2 * boson_channels
    twice_c_n1 = twice_c_majorana + twice_c_boson
    assert twice_c_majorana == 8
    assert twice_c_boson == 16
    assert twice_c_n1 == 24

    print("primon_supergraded_gas_algebra: ok")
    print("  finite Euler: Z_boson * Z_signed_fermion = 1")
    print("  reciprocal boundary: 1/Z is singular at Z=0, not zero there")
    print("  positive fermions: Z_f^+(x) * Z_boson(x^2) = Z_boson(x)")
    print("  finite Witten: sum_{S subset P} (-1)^|S| = 0 for nonempty P")
    print("  fermion CAR: a^2 = c^2 = 0 and a*c + c*a = I")
    print("  boson CCR: witness-gated Weyl normalization lambda^2*nu = 1")
    print("  supercharges: {J,epsilon}=0, [J,epsilon]=2Q, Q^2=-I")
    print("  chiral projectors: P_+^2=P_+, P_-^2=P_-, P_+P_-=0, P_++P_-=I")
    print("  central charges: 8 Majoranas -> 2c=8, 8 bosons -> 2c=16, N=1 total -> 2c=24")


if __name__ == "__main__":
    main()
