#!/usr/bin/env python3
"""Finite witness for the E8 Z3 grading dimension packet.

This checks only the dimension bookkeeping

    248 = (8 + 78) + (3 * 27) + (3 * 27)

and a diagonal order-three grading matrix with multiplicities 86, 81, 81.
It does not construct the Lie algebra E8, SU(3), E6, or Standard Model
representations.
"""

from __future__ import annotations

import sympy as sp


def main() -> None:
    su3_adjoint_dim = 8
    e6_adjoint_dim = 78
    e6_matter_dim = 27
    generation_multiplicity = 3
    e8_adjoint_dim = 248

    neutral_dim = su3_adjoint_dim + e6_adjoint_dim
    flow_dim = generation_multiplicity * e6_matter_dim
    total_dim = neutral_dim + flow_dim + flow_dim

    omega = sp.Rational(-1, 2) + sp.sqrt(3) * sp.I / 2
    grading_diagonal = [1] * neutral_dim + [omega] * flow_dim + [omega**2] * flow_dim
    grading = sp.diag(*grading_diagonal)

    cube_is_identity = sp.simplify(grading**3 - sp.eye(e8_adjoint_dim)) == sp.zeros(e8_adjoint_dim)
    multiplicities = {
        "neutral": grading_diagonal.count(1),
        "omega": grading_diagonal.count(omega),
        "omega_squared": grading_diagonal.count(omega**2),
    }

    print("E8 Z3 finite dimension witness")
    print(f"1. Neutral dimension 8 + 78 = {neutral_dim}: {neutral_dim == 86}")
    print(f"2. Flow dimension 3 * 27 = {flow_dim}: {flow_dim == 81}")
    print(f"3. Total split 86 + 81 + 81 = {total_dim}: {total_dim == e8_adjoint_dim}")
    print(f"4. Grading multiplicities: {multiplicities}")
    print(f"5. Diagonal Z3 grading cubes to identity: {cube_is_identity}")


if __name__ == "__main__":
    main()
