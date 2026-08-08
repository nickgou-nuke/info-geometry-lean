#!/usr/bin/env python3
"""SymPy witness for Krein null-space geometry and Moore-Penrose/Drazin cores.

Model:
    carrier = exact ⊕ coexact ⊕ harmonic

The harmonic mode is the horizon/null boundary.  A degenerate operator L kills
that harmonic mode.  Its Moore-Penrose/Drazin inverse inverts only the core and
leaves the boundary projected out.
"""

import sympy as sp


def assert_zero(name: str, expr: sp.Expr) -> None:
    simplified = sp.simplify(expr)
    assert simplified == 0, f"{name} failed: {simplified}"
    print(f"OK  {name}")


def assert_matrix_zero(name: str, mat: sp.Matrix) -> None:
    simplified = mat.applyfunc(sp.simplify)
    assert simplified == sp.zeros(*mat.shape), f"{name} failed:\n{simplified}"
    print(f"OK  {name}")


I3 = sp.eye(3)

P_exact = sp.diag(1, 0, 0)
P_coexact = sp.diag(0, 1, 0)
P_harmonic = sp.diag(0, 0, 1)
P_core = P_exact + P_coexact

# Degenerate Krein/Laplacian carrier: harmonic horizon is in the kernel.
L = sp.diag(1, 1, 0)
L_mp = sp.diag(1, 1, 0)
L_drazin = sp.diag(1, 1, 0)

assert_matrix_zero("Hodge projector decomposition", P_exact + P_coexact + P_harmonic - I3)
for name, P in [("exact", P_exact), ("coexact", P_coexact), ("harmonic", P_harmonic), ("core", P_core)]:
    assert_matrix_zero(f"{name} projector idempotent", P * P - P)

assert_matrix_zero("exact and coexact are orthogonal", P_exact * P_coexact)
assert_matrix_zero("exact and harmonic are orthogonal", P_exact * P_harmonic)
assert_matrix_zero("coexact and harmonic are orthogonal", P_coexact * P_harmonic)

assert_matrix_zero("L kills harmonic boundary", L * P_harmonic)
assert_matrix_zero("L acts as identity on core", L * P_core - P_core)

# Moore-Penrose equations for this self-adjoint diagonal model.
assert_matrix_zero("MP: L L+ L = L", L * L_mp * L - L)
assert_matrix_zero("MP: L+ L L+ = L+", L_mp * L * L_mp - L_mp)
assert_matrix_zero("MP: L L+ is core projector", L * L_mp - P_core)
assert_matrix_zero("MP: L+ L is core projector", L_mp * L - P_core)

# Drazin equations for index-one singular operator.
assert_matrix_zero("Drazin commutes", L * L_drazin - L_drazin * L)
assert_matrix_zero("Drazin core inverse", L_drazin * L * L_drazin - L_drazin)
assert_matrix_zero("Drazin extracts non-null core", L * L_drazin - P_core)

x0, x1, x2, r = sp.symbols("x0 x1 x2 r", real=True)
v = sp.Matrix([x0, x1, x2])
core_v = P_core * v
harm_v = P_harmonic * v
assert_matrix_zero("vector decomposes into core plus harmonic", core_v + harm_v - v)

# Dikin ellipsoid of the core Hessian.  The harmonic coordinate is invisible to
# the degenerate Hessian and lives at the conformal/parabolic boundary.
H_core = P_core
dikin_quadratic = (core_v.T * H_core * core_v)[0]
assert_zero("Dikin ellipsoid ignores harmonic horizon coordinate", dikin_quadratic - (x0**2 + x1**2))

print("OK  Moore-Penrose/Drazin inverse extracts the Krein core and leaves harmonic horizon")
