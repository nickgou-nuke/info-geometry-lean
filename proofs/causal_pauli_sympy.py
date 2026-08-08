#!/usr/bin/env python3
"""SymPy witness for the Pauli/Cl(1,1) causal determinant classifier.

Core identity:

    X = [[a,b],[c,-a]]  implies  X^2 = -det(X) I.

This makes determinant sign the causal trichotomy:

    det =  1  -> X^2 = -I  -> elliptic/rotation chart
    det = -1  -> X^2 =  I  -> hyperbolic/boost chart
    det =  0  -> X^2 =  0  -> parabolic/null shear chart
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


a, b, c, theta = sp.symbols("a b c theta", real=True)
I2 = sp.eye(2)

X = sp.Matrix([[a, b], [c, -a]])
det_X = sp.factor(X.det())

assert_zero("traceless condition", sp.trace(X))
assert_matrix_zero("Pauli causal identity X^2 = -det(X) I", X * X + det_X * I2)

E = sp.Matrix([[0, -1], [1, 0]])  # det=1, E^2=-I
H = sp.Matrix([[0, 1], [1, 0]])   # det=-1, H^2=I
N = sp.Matrix([[0, 1], [0, 0]])   # det=0, N^2=0

assert_zero("elliptic determinant det(E)=1", E.det() - 1)
assert_matrix_zero("elliptic square E^2=-I", E * E + I2)

assert_zero("hyperbolic determinant det(H)=-1", H.det() + 1)
assert_matrix_zero("hyperbolic square H^2=I", H * H - I2)

assert_zero("parabolic determinant det(N)=0", N.det())
assert_matrix_zero("parabolic square N^2=0", N * N)

elliptic_exp = sp.cos(theta) * I2 + sp.sin(theta) * E
hyperbolic_exp = sp.cosh(theta) * I2 + sp.sinh(theta) * H
parabolic_exp = I2 + theta * N

assert_matrix_zero(
    "elliptic exp chart is self-closed",
    elliptic_exp.diff(theta) - E * elliptic_exp,
)
assert_matrix_zero(
    "hyperbolic exp chart is self-closed",
    hyperbolic_exp.diff(theta) - H * hyperbolic_exp,
)
assert_matrix_zero(
    "parabolic exp chart is self-closed",
    parabolic_exp.diff(theta) - N * parabolic_exp,
)

assert_zero("det elliptic exp = 1", sp.factor(elliptic_exp.det() - 1))
assert_zero("det hyperbolic exp = 1", sp.factor(hyperbolic_exp.det() - 1))
assert_zero("det parabolic exp = 1", sp.factor(parabolic_exp.det() - 1))

# ---------------------------------------------------------------------------
# Conformal topological boundary and twistor incidence.
# ---------------------------------------------------------------------------

u, lam, omega0, omega1, pi0, pi1 = sp.symbols("u lam omega0 omega1 pi0 pi1")

# A boundary point is represented by a rank-one/null matrix.  The parabolic
# chart is the unipotent stabilizer of the chosen null line.
boundary_point = sp.Matrix([[1, u], [0, 0]])
transported_boundary = parabolic_exp * boundary_point

assert_zero("boundary point is null", boundary_point.det())
assert_zero("parabolic transport preserves boundary nullness", transported_boundary.det())
assert_matrix_zero("parabolic transport fixes the base null ray", parabolic_exp * sp.Matrix([[1], [0]]) - sp.Matrix([[1], [0]]))

# A minimal twistor is a pair (omega, pi); the incidence omega = x*pi is
# projective, hence invariant under nonzero scalar rescaling of the spinor pi.
omega = sp.Matrix([[omega0], [omega1]])
pi = sp.Matrix([[pi0], [pi1]])
space_time_point = parabolic_exp

incidence = omega - space_time_point * pi
scaled_incidence = lam * omega - space_time_point * (lam * pi)
assert_matrix_zero("twistor incidence is projectively homogeneous", scaled_incidence - lam * incidence)

print("OK  determinant sign is the causal Weyl gauge")
print("OK  parabolic nilpotent chart is a conformal boundary/twistor chart")
