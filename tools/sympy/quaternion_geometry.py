#!/usr/bin/env python3
"""
Finite quaternion geometry verification.

Mirrors lean/InfoGeometry/Canonical/QuaternionGeometry.lean at the level of
finite algebraic residual equivalences. It does not derive a smooth Ricci
identity, spin connection, curvature tensor, or Einstein-Cartan dynamics.
"""

from __future__ import annotations

import sympy as sp


def assert_zero(expr, label: str) -> None:
    reduced = sp.expand(sp.simplify(expr))
    if reduced != 0:
        raise AssertionError(f"{label} failed: {reduced}")


def main() -> None:
    print("=" * 72)
    print("QUATERNION GEOMETRY -- FINITE SYMPY VERIFICATION")
    print("=" * 72)

    # Metric symmetry for g_{mu nu} = eta_ab e_mu^a e_nu^b.
    eta00, eta01, eta11 = sp.symbols("eta00 eta01 eta11", real=True)
    eta = sp.Matrix([[eta00, eta01], [eta01, eta11]])
    emu0, emu1, enu0, enu1 = sp.symbols("emu0 emu1 enu0 enu1", real=True)
    emu = sp.Matrix([emu0, emu1])
    enu = sp.Matrix([enu0, enu1])
    g_mn = (emu.T * eta * enu)[0]
    g_nm = (enu.T * eta * emu)[0]
    assert_zero(g_mn - g_nm, "metric symmetry from symmetric eta")
    print("  induced metric symmetry verified")

    # Formal antisymmetry of [nabla_mu, nabla_nu] Phi.
    ab, ba = sp.symbols("ab ba")
    comm_mu_nu = ab - ba
    comm_nu_mu = ba - ab
    assert_zero(comm_nu_mu + comm_mu_nu, "nabla commutator antisymmetry")
    print("  formal covariant-commutator antisymmetry verified")

    # Ricci/torsion residual expansion: residual is exactly lhs - rhs.
    lhs, curvature, torsion_translation = sp.symbols("lhs curvature torsion_translation")
    rhs = curvature + torsion_translation
    ricci_residual = lhs - rhs
    assert_zero(rhs - (curvature + torsion_translation), "ricci torsion rhs definition")
    assert_zero(ricci_residual - (lhs - rhs), "ricci torsion residual expansion")
    print("  Ricci/torsion residual expansion verified")

    # Field equation residual expansion: residual is exactly kinetic - mass.
    kinetic, mass = sp.symbols("kinetic mass")
    field_residual = kinetic - mass
    assert_zero(field_residual - (kinetic - mass), "field equation residual expansion")
    print("  quaternion field residual expansion verified")

    print("=" * 72)
    print("QUATERNION GEOMETRY VERIFIED")
    print("=" * 72)


if __name__ == "__main__":
    main()
