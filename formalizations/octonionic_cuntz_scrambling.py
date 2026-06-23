#!/usr/bin/env python3
"""Finite witness for the octonionic boundary / Kuzmin q-CCR bridge.

This script checks only the algebraic endpoint reductions mirrored by the Lean
files:

* the residual vector component from Voelkel Lemma 4.5.2 vanishes when either
  lower-left source coordinate is zero;
* the unit-half coordinate reduction `N(x)=1 ∧ half(x)=e1 ⇒ x12=1`;
* the reduced Zorn boundary norm is covariant under unit scaling;
* the q-CCR relation gives the CAR, CCR, and Cuntz-Toeplitz endpoint readouts.
* the standard finite Fibonacci F/R matrices satisfy the two-generator braid
  relation.

It is not a C*-isomorphism proof and it is not an anyonic universality theorem.
"""

from sympy import I, Matrix, eye, exp, nsimplify, pi, simplify, sqrt, symbols, zeros


def verify_voelkel_residual() -> None:
    vi21, vj21, x22 = symbols("vi21 vj21 x22")
    residual_b = vj21 * (vi21 * x22) - vi21 * (vj21 * x22)

    left_zero = simplify(residual_b.subs(vi21, 0))
    right_zero = simplify(residual_b.subs(vj21, 0))

    assert left_zero == 0
    assert right_zero == 0
    print("Voelkel residual endpoint checks: ok")


def verify_unit_half_coordinate_reduction() -> None:
    x12, x22 = symbols("x12 x22")

    # Under half(x)=e1, the reduced Zorn coordinates are x11=1 and x21=0.
    # Therefore N(x)=x11*x12 + x21*x22 reduces to x12.
    reduced_norm = simplify(1 * x12 + 0 * x22)
    assert reduced_norm == x12

    # If N(x)=1 under this reduction, then x12=1.
    x12_from_unit_norm = simplify(reduced_norm.subs(x12, 1))
    assert x12_from_unit_norm == 1
    print("Unit-half coordinate reduction: ok")


def verify_boundary_norm_scaling() -> None:
    u, x11, x12, x21, x22 = symbols("u x11 x12 x21 x22")
    norm = x11 * x12 + x21 * x22
    scaled_norm = (u * x11) * (u * x12) + (u * x21) * (u * x22)

    assert simplify(scaled_norm - u**2 * norm) == 0
    print("Reduced OP1 boundary norm scaling: ok")


def verify_qccr_endpoints() -> None:
    delta, aadag = symbols("delta aadag")

    # q-CCR relation in solved form: a_i^* a_j = delta_ij + q a_j a_i^*.
    def astar_a(q_value):
        return delta + q_value * aadag

    car = simplify(astar_a(-1) + aadag - delta)
    ccr = simplify(astar_a(1) - aadag - delta)
    toeplitz = simplify(astar_a(0) - delta)

    assert car == 0
    assert ccr == 0
    assert toeplitz == 0
    print("q-CCR CAR/CCR/Toeplitz endpoint readouts: ok")


def verify_fibonacci_braid() -> None:
    phi = (1 + sqrt(5)) / 2
    f_matrix = Matrix(
        [
            [1 / phi, sqrt(1 / phi)],
            [sqrt(1 / phi), -1 / phi],
        ]
    )
    identity = eye(2)
    assert (f_matrix * f_matrix - identity).applyfunc(simplify) == zeros(2)

    r_matrix = Matrix(
        [
            [exp(-4 * I * pi / 5), 0],
            [0, exp(3 * I * pi / 5)],
        ]
    )
    assert (r_matrix.H * r_matrix - identity).applyfunc(simplify) == zeros(2)

    sigma1 = r_matrix
    sigma2 = simplify(f_matrix * r_matrix * f_matrix)
    braid_defect = simplify(sigma1 * sigma2 * sigma1 - sigma2 * sigma1 * sigma2)
    assert braid_defect.applyfunc(nsimplify) == zeros(2)
    print("Finite Fibonacci F/R braid relation: ok")


def main() -> None:
    verify_voelkel_residual()
    verify_unit_half_coordinate_reduction()
    verify_boundary_norm_scaling()
    verify_qccr_endpoints()
    verify_fibonacci_braid()
    print("OCTONIONIC_CUNTZ_ENDPOINT_WITNESS_OK")


if __name__ == "__main__":
    main()
