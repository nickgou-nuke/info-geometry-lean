"""SymPy witness for the local Cl(1,1) Clifford atom.

Checks the same finite identities formalized in `AtomicCliffordKAN.lean`:
- e1^2 = +I, e2^2 = -I, {e1,e2}=0
- sigmaPlus^2 = 0
- K N A atomic normal form
- Witten supertrace Tr(sigma3 K N A)
- pure squeeze limit 2*sinh(alpha)
- chirality projectors P+, P-, P0
- split paravector determinant/light-cone form
- finite tensor-network product over prime-labelled modes
"""

import sympy as sp


def assert_zero(name, expr):
    simplified = sp.simplify(sp.expand_func(expr).rewrite(sp.exp))
    if simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")


def assert_matrix_zero(name, M):
    S = sp.simplify(M)
    if S != sp.zeros(*S.shape):
        raise AssertionError(f"{name} failed:\n{S}")


theta, alpha, n = sp.symbols("theta alpha n", real=True)
t, p, w, z = sp.symbols("t p w z", real=True)
a2, a3, a5 = sp.symbols("a2 a3 a5", real=True)

I2 = sp.eye(2)
sigma3 = sp.Matrix([[1, 0], [0, -1]])
i_sigma2 = sp.Matrix([[0, 1], [-1, 0]])
sigma_plus = sp.Matrix([[0, 1], [0, 0]])

# Clifford relations and nilpotent sector.
assert_matrix_zero("sigma3^2 = I", sigma3 * sigma3 - I2)
assert_matrix_zero("i_sigma2^2 = -I", i_sigma2 * i_sigma2 + I2)
assert_matrix_zero("anticommutator", sigma3 * i_sigma2 + i_sigma2 * sigma3)
assert_matrix_zero("sigmaPlus^2", sigma_plus * sigma_plus)
assert_matrix_zero("sigma3^3 = sigma3", sigma3**3 - sigma3)

# Chirality projections.
Pplus = sp.Rational(1, 2) * (I2 + sigma3)
Pminus = sp.Rational(1, 2) * (I2 - sigma3)
Pzero = I2 - sigma3 * sigma3
assert_matrix_zero("Pplus", Pplus - sp.Matrix([[1, 0], [0, 0]]))
assert_matrix_zero("Pminus", Pminus - sp.Matrix([[0, 0], [0, 1]]))
assert_matrix_zero("Pzero", Pzero)

# Atomic KNA normal form.  This ordering is the one whose closed form is
# e^alpha cos theta, e^-alpha(n cos theta - sin theta), ...
K = sp.Matrix([[sp.cos(theta), -sp.sin(theta)], [sp.sin(theta), sp.cos(theta)]])
A = sp.diag(sp.exp(alpha), sp.exp(-alpha))
N = sp.Matrix([[1, n], [0, 1]])
KNA = sp.simplify(K * N * A)
expected = sp.Matrix([
    [sp.exp(alpha) * sp.cos(theta), sp.exp(-alpha) * (n * sp.cos(theta) - sp.sin(theta))],
    [sp.exp(alpha) * sp.sin(theta), sp.exp(-alpha) * (n * sp.sin(theta) + sp.cos(theta))],
])
assert_matrix_zero("KNA normal form", KNA - expected)

supertrace = sp.simplify(sp.trace(sigma3 * KNA))
expected_supertrace = 2 * sp.sinh(alpha) * sp.cos(theta) - n * sp.exp(-alpha) * sp.sin(theta)
assert_zero("atomic Witten supertrace", supertrace - expected_supertrace)
assert_zero("pure squeeze", supertrace.subs({theta: 0, n: 0}) - 2 * sp.sinh(alpha))

# Split traceless and paravector determinant forms.
traceless = sp.Matrix([[z, p + w], [w - p, -z]])
assert_zero("traceless split det", traceless.det() - (p**2 - w**2 - z**2))
assert_zero("traceless supertrace extracts z", sp.trace(sigma3 * traceless) - 2 * z)

paravector = sp.Matrix([[t + z, p + w], [w - p, t - z]])
assert_zero("paravector split det", paravector.det() - (t**2 + p**2 - w**2 - z**2))

# Finite prime-labelled tensor approximation.
finite_bulk = sp.prod(2 * sp.sinh(a) for a in [a2, a3, a5])
expected_bulk = 2 * sp.sinh(a2) * 2 * sp.sinh(a3) * 2 * sp.sinh(a5)
assert_zero("finite prime-mode tensor product", finite_bulk - expected_bulk)

print("OK atomic Clifford KAN/Witten SymPy witness completed")
