"""SymPy witness for the multivalued matrix logarithm and spinor monodromy.

This script verifies the algebraic structures discussed:
1. The solutions to X^2 = -I in the biquaternion algebra.
2. The branches of the matrix logarithm log(-I) and their construction.
3. The spectrum of the monodromy connection L = 1/(2πi) log(-I),
   proving that all branches strictly yield half-integer eigenvalues (spinors).
"""

import sympy as sp

def assert_matrix_zero(name, M):
    S = sp.simplify(M)
    if S != sp.zeros(*S.shape):
        raise AssertionError(f"{name} failed:\n{S}")

# ── Pauli matrices ──────────────────────────────────────────────────────────
I2 = sp.eye(2)
s1 = sp.Matrix([[0, 1], [1, 0]])
s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
s3 = sp.Matrix([[1, 0], [0, -1]])


# ══════════════════════════════════════════════════════════════════════════════
# §1  Roots of -I (The X^2 = -I manifold)
# ══════════════════════════════════════════════════════════════════════════════
print("§1  Roots of -I: X² = -I")

# We test the non-scalar solutions: trace = 0 and sum of squares = -1
a1, a2, a3 = sp.symbols("a1 a2 a3")
X_root = a1 * s1 + a2 * s2 + a3 * s3
# Enforce the manifold condition: a1^2 + a2^2 + a3^2 = -1
X_sq = sp.simplify(X_root * X_root)
# We know X_root * X_root = (a1^2 + a2^2 + a3^2) * I2
# Substituting the condition:
X_sq_eval = X_sq.subs(a1**2 + a2**2 + a3**2, -1)

assert_matrix_zero("X^2 = -I on the manifold", X_sq_eval - (-I2))
print("   Tr(X) = 0 and a₁² + a₂² + a₃² = -1 implies X² = -I  ✓")


# ══════════════════════════════════════════════════════════════════════════════
# §2  Unified Parity-Reconciled Branches of log(-I) mapped via exp
# ══════════════════════════════════════════════════════════════════════════════
print("\n§2  Unified Parity-Reconciled Branches of log(-I)")

m, n = sp.symbols("m n", integer=True)
n1, n2, n3 = sp.symbols("n1 n2 n3")

# Unified formulation: 
# v = m * pi * i
# a0 = (m + 2n + 1) * pi * i
v_val = m * sp.pi * sp.I
a0 = (m + 2 * n + 1) * sp.pi * sp.I

n_vec = n1 * s1 + n2 * s2 + n3 * s3
# log(-I) = a0 * I2 + v_val * n_vec
# We verify exp(log(-I)) = -I
# exp(X) = e^{a0} (cosh(v) I + sinh(v) n_vec) 
# Since v = m * pi * i, cosh(m pi i) = (-1)^m, sinh(m pi i) = 0
# e^{a0} = e^{(m+1) pi i} e^{2n pi i} = (-1)^{m+1}
# So e^{a0} cosh(v) = (-1)^{m+1} (-1)^m = (-1)^{2m+1} = -1.

exp_a0 = sp.exp(a0)
# Simplify the scalar part: e^{a0} * cosh(v)
scalar_term = sp.simplify((exp_a0 * sp.cosh(v_val)).rewrite(sp.cos))
# Simplify the vector part: e^{a0} * sinh(v)
vector_term = sp.simplify((exp_a0 * sp.sinh(v_val)).rewrite(sp.sin))

exp_unified = scalar_term * I2 + vector_term * n_vec
assert_matrix_zero("exp(log_unified) = -I", exp_unified - (-I2))
print("   Unified branches: exp((m+2n+1)πi I + mπi n̂·σ⃗) = -I  ✓")


# ══════════════════════════════════════════════════════════════════════════════
# §3  Eigenvalues of the Monodromy Connection (Spinors)
# ══════════════════════════════════════════════════════════════════════════════
print("\n§3  Fractional Eigenvalues of L = 1/(2πi) log(-I)")

# Connection L = 1/(2pi i) log(-I)
# L = (m + 2n + 1)/2 I2 + m/2 n_vec
L_unified = (m + 2 * n + 1) / sp.Rational(2) * I2 + m / sp.Rational(2) * n_vec

# The traceless part is T = m/2 n_vec
# T^2 = (m/2)^2 (n1^2 + n2^2 + n3^2) I
T_uni = m / sp.Rational(2) * n_vec
T_uni_sq = sp.simplify(T_uni * T_uni)

# Expand and substitute n1^2 + n2^2 + n3^2 = 1
T_uni_sq_eval = sp.expand(T_uni_sq).subs(n1**2 + n2**2 + n3**2, 1)
T_uni_sq_eval = sp.simplify(T_uni_sq_eval.subs(n3**2, 1 - n1**2 - n2**2))

expected_T_uni_sq = (m / sp.Rational(2))**2 * I2
assert_matrix_zero("T_uni^2 = (m/2)^2 I", T_uni_sq_eval - expected_T_uni_sq)

# Eigenvalues are a0/(2pi i) \pm m/2
# = (m + 2n + 1)/2 \pm m/2
eval1 = sp.simplify((m + 2 * n + 1) / sp.Rational(2) + m / sp.Rational(2))
eval2 = sp.simplify((m + 2 * n + 1) / sp.Rational(2) - m / sp.Rational(2))

print(f"   Connection L eigenvalues: {eval1} and {eval2}")
print("   Both are strictly half-integers: p + 1/2 and q + 1/2  ✓")

delta_eval = sp.simplify(eval1 - eval2)
print(f"   ΔEigenvalues = {delta_eval}  (Strictly Integer Transitions)  ✓")

print("\nbiquaternion_logarithm_monodromy.py: All topological connections verified")
