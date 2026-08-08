import sympy as sp


I2 = sp.eye(2)

# Real 2x2 representatives of the three rank-one real geometries.
# J replaces the scalar complex i by an oriented bivector/rotor.
J = sp.Matrix([[0, -1], [1, 0]])   # elliptic: J^2 = -1
K = sp.Matrix([[1, 0], [0, -1]])   # hyperbolic: K^2 = +1
N = sp.Matrix([[0, 1], [0, 0]])    # parabolic: N^2 = 0

assert J**2 == -I2
assert K**2 == I2
assert N**2 == sp.zeros(2)


def square_classifier(U):
    if sp.simplify(U**2 + I2) == sp.zeros(2):
        return "elliptic"
    if sp.simplify(U**2 - I2) == sp.zeros(2):
        return "hyperbolic"
    if sp.simplify(U**2) == sp.zeros(2):
        return "parabolic"
    return "unclassified"


assert square_classifier(J) == "elliptic"
assert square_classifier(K) == "hyperbolic"
assert square_classifier(N) == "parabolic"


def determinant_sign_classifier(A):
    det = sp.simplify(A.det())
    if det == 0:
        return "parabolic/degenerate"
    if det.is_positive:
        return "elliptic/orientation-preserving"
    if det.is_negative:
        return "hyperbolic/orientation-reversing"
    return "symbolic"


assert determinant_sign_classifier(J) == "elliptic/orientation-preserving"
assert determinant_sign_classifier(K) == "hyperbolic/orientation-reversing"
assert determinant_sign_classifier(N) == "parabolic/degenerate"

# OP^3 = OP is the cubic projector/trifactor condition.
OP = sp.diag(1, 0)
Q = sp.diag(1, -1)
R = sp.diag(1, 0, -1)

for A in (OP, Q, R):
    assert A**3 == A
    assert A * (A - sp.eye(A.rows)) * (A + sp.eye(A.rows)) == sp.zeros(A.rows)

# Pauli involution: conjugation by sigma_z grades the real Pauli algebra into
# even and odd pieces.
sigma_x = sp.Matrix([[0, 1], [1, 0]])
sigma_y_real = J
sigma_z = K


def grade_involution(A):
    return sp.simplify(sigma_z * A * sigma_z)


assert grade_involution(I2) == I2
assert grade_involution(sigma_z) == sigma_z
assert grade_involution(sigma_x) == -sigma_x
assert grade_involution(sigma_y_real) == -sigma_y_real


def even_part(A):
    return sp.simplify((A + grade_involution(A)) / 2)


def odd_part(A):
    return sp.simplify((A - grade_involution(A)) / 2)


a, b, c, d = sp.symbols("a b c d")
A = a * I2 + b * sigma_x + c * sigma_y_real + d * sigma_z
assert sp.simplify(even_part(A) - (a * I2 + d * sigma_z)) == sp.zeros(2)
assert sp.simplify(odd_part(A) - (b * sigma_x + c * sigma_y_real)) == sp.zeros(2)

# Finite prime-mode graded arithmetic determinant:
# Str((-1)^F exp(-sH)) = product_p (1 - p^(-s)).
x2, x3, x5 = sp.symbols("x2 x3 x5")
finite_graded = sp.expand((1 - x2) * (1 - x3) * (1 - x5))
finite_supertrace = sp.expand(
    1
    - (x2 + x3 + x5)
    + (x2 * x3 + x2 * x5 + x3 * x5)
    - x2 * x3 * x5
)
assert finite_graded == finite_supertrace

# Local reciprocal-pole model: if zeta(s) = c(s-rho), then the graded index
# 1/zeta(s) has inverse determinant singularity 1/(c(s-rho)).
s, rho, c0 = sp.symbols("s rho c0", nonzero=True)
zeta_local = c0 * (s - rho)
graded_index_local = 1 / zeta_local
assert sp.simplify(graded_index_local * zeta_local) == 1

print("SouriauHestenesMobiusPole.py: operator grading and reciprocal pole model verified")
