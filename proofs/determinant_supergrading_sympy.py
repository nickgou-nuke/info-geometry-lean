import sympy as sp

# 2x2 real doubled-sheet model
J = sp.Matrix([[0, 1], [1, 0]])          # modular_j: sheet swap
epsilon = sp.Matrix([[1, 0], [0, -1]])    # chiralParity: grading operator
K = J * epsilon                          # emergent complex structure J ε


def det_grade(M: sp.Matrix) -> sp.Integer:
    """Determinant sign as the supergrading value in {+1,-1,0}."""
    return sp.sign(M.det())

# Basic involutions and determinant signs
assert J.det() == -1
assert epsilon.det() == -1
assert K.det() == 1

assert J * J == sp.eye(2)
assert epsilon * epsilon == sp.eye(2)
assert K * K == -sp.eye(2)

# Odd/even behavior from determinant sign
assert det_grade(J) == -1
assert det_grade(epsilon) == -1
assert det_grade(K) == 1
assert det_grade(J * epsilon) == det_grade(J) * det_grade(epsilon)
assert det_grade(epsilon * K) == det_grade(epsilon) * det_grade(K)

# Multiplicative conservation across all pairings
pairs = [
    (sp.eye(2), sp.eye(2), 1, 1),
    (sp.eye(2), epsilon, 1, -1),
    (epsilon, sp.eye(2), -1, 1),
    (epsilon, epsilon, -1, -1),
]
for A, B, gA, gB in pairs:
    lhs = det_grade(A * B)
    rhs = gA * gB
    assert lhs == rhs

# Anticommutation J ε = -ε J
assert J * epsilon == - (epsilon * J)

# Supertrace witness STr(rho)=Tr(epsilon*rho)=rho_00-rho_11
a, b, c, d = sp.symbols('a b c d', real=True)
rho = sp.Matrix([[a, b], [c, d]])
supertrace = (epsilon * rho).trace().simplify()
assert sp.simplify(supertrace - (a - d)) == 0

# Balanced sheet volume (Klein-boundary style): equal diagonal entries cancel
rho_balanced = sp.Matrix([[a, b], [c, a]])
assert sp.simplify((epsilon * rho_balanced).trace()) == 0

print("determinant_supergrading_sympy: all checks passed")
