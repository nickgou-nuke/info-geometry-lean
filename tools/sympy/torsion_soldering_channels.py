#!/usr/bin/env python3
"""Coordinate-free torsion soldering channel checks.

This verifies the algebraic identities of the torsion 2-form across
the spinor, vector, and quaternion channels, complementing Section 12.
It verifies that T = dE + [\Omega, E] (or appropriate left/right actions)
is structurally preserved by the channel soldering maps.
"""

from __future__ import annotations
import sympy as sp
from coordinate_free_connection_channels import (
    assert_matrix_zero, commutator,
    spinor_channel, vector_channel, quaternion_channel,
    symbolic_matrix
)

def covariant_exterior_derivative(
    de_xy: sp.Matrix, de_yx: sp.Matrix,
    omega_x: sp.Matrix, e_y: sp.Matrix,
    omega_y: sp.Matrix, e_x: sp.Matrix,
    action_type: str = "commutator"
) -> sp.Matrix:
    """Computes the torsion 2-form T(X,Y) = de(X,Y) + (Omega_X e_Y - Omega_Y e_X)."""
    de = de_xy - de_yx
    if action_type == "commutator":
        return de + commutator(omega_x, e_y) - commutator(omega_y, e_x)
    elif action_type == "left":
        return de + omega_x * e_y - omega_y * e_x
    else:
        raise ValueError("Unknown action_type")

def verify_torsion_channel(name: str, channel, n: int, action_type: str) -> None:
    print(f"\nTorsion {name} channel ({action_type} action)")
    de_xy = symbolic_matrix(f"{name}_dexy_", n)
    de_yx = symbolic_matrix(f"{name}_deyx_", n)
    omega_x = symbolic_matrix(f"{name}_wx_", n)
    e_y = symbolic_matrix(f"{name}_ey_", n)
    omega_y = symbolic_matrix(f"{name}_wy_", n)
    e_x = symbolic_matrix(f"{name}_ex_", n)

    base_torsion = covariant_exterior_derivative(
        de_xy, de_yx, omega_x, e_y, omega_y, e_x, action_type
    )
    image_torsion = covariant_exterior_derivative(
        channel(de_xy), channel(de_yx),
        channel(omega_x), channel(e_y),
        channel(omega_y), channel(e_x),
        action_type
    )
    
    assert_matrix_zero("channel preserves torsion", channel(base_torsion) - image_torsion)
    
    # Antisymmetry T(X, Y) = -T(Y, X)
    swapped_torsion = covariant_exterior_derivative(
        channel(de_yx), channel(de_xy),
        channel(omega_y), channel(e_x),
        channel(omega_x), channel(e_y),
        action_type
    )
    assert_matrix_zero("image torsion is antisymmetric", image_torsion + swapped_torsion)


def main() -> int:
    print("=" * 72)
    print("TORSION SOLDERING CHANNELS")
    print("=" * 72)

    verify_torsion_channel("spinor", spinor_channel, 2, "left")
    verify_torsion_channel("vector", vector_channel, 2, "commutator")
    verify_torsion_channel("quaternion", quaternion_channel, 2, "commutator")

    print("\nTORSION SOLDERING CHANNELS VERIFIED")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
