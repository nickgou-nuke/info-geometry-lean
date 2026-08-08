"""SymPy witness: negative identity roots and multivalued logarithms in M2(C).

Verifies the Pauli/biquaternion formula

  X = a0 I + T,  T = a1 σ1 + a2 σ2 + a3 σ3,  v^2 = a1^2+a2^2+a3^2
  X^k = A_k I + B_k T

where
  A_k = ((a0+v)^k + (a0-v)^k)/2
  B_k = ((a0+v)^k - (a0-v)^k)/(2v).

Then X^k=-I iff both eigenvalues a0±v are k-th roots of -1
(for the diagonalizable/nondegenerate v != 0 case).  Also verifies the
multivalued matrix logarithm mechanism on a concrete spinorial monodromy:
log eigenvalues differ by 2πi branch shifts, but exponentiate to the same
monodromy matrix.
"""

import sympy as sp


def assert_zero(name, expr):
    s = sp.simplify(sp.expand(expr))
    if s != 0:
        raise AssertionError(f"{name} failed: {s}")


def assert_matrix_zero(name, M):
    S = sp.simplify(M)
    if S != sp.zeros(*S.shape):
        raise AssertionError(f"{name} failed:\n{S}")


I2 = sp.eye(2)
s1 = sp.Matrix([[0, 1], [1, 0]])
s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
s3 = sp.Matrix([[1, 0], [0, -1]])

print("§1  Cayley-Hamilton/Pauli power formula")
a0, a1, a2, a3, v = sp.symbols("a0 a1 a2 a3 v")
T = a1 * s1 + a2 * s2 + a3 * s3
X = a0 * I2 + T
r2 = a1**2 + a2**2 + a3**2
assert_matrix_zero("T^2 = r^2 I", T * T - r2 * I2)

# Verify the closed power formula for a range of k after imposing v^2=r2.
for k in range(1, 9):
    A = ((a0 + v) ** k + (a0 - v) ** k) / 2
    B = ((a0 + v) ** k - (a0 - v) ** k) / (2 * v)
    formula = A * I2 + B * T
    # v*diff is polynomial; reduce v^2 -> r2.
    diff = sp.expand(v * (X**k - formula))
    reduced = diff.applyfunc(lambda e: sp.rem(sp.Poly(sp.expand(e), v), sp.Poly(v**2 - r2, v)).as_expr())
    assert_matrix_zero(f"power formula k={k}", reduced)
print("   X^k = A_k I + B_k T verified for k=1..8 ✓")

print("§2  Classification test: X^k = -I from eigenvalue roots of -1")
k = 5
m1, m2 = 1, 3
lam1 = sp.exp(sp.I * (sp.pi + 2 * sp.pi * m1) / k)
lam2 = sp.exp(sp.I * (sp.pi + 2 * sp.pi * m2) / k)
a0v = sp.simplify((lam1 + lam2) / 2)
vv = sp.simplify((lam1 - lam2) / 2)
# Choose vector part along σ3, so T = v σ3 and X has eigenvalues a0±v.
Xroot = a0v * I2 + vv * s3
assert_matrix_zero("X^k = -I", sp.simplify(Xroot**k + I2))
print("   eigenvalues λ1,λ2 with λj^k=-1 give X^k=-I ✓")

print("§3  Square roots of -I: scalar and traceless spinorial families")
assert_matrix_zero("(iI)^2=-I", (sp.I * I2) ** 2 + I2)
assert_matrix_zero("(-iI)^2=-I", (-sp.I * I2) ** 2 + I2)
# Non-scalar example: σ2 squares to +I, so iσ2 squares to -I.
Q = sp.I * s2
assert_matrix_zero("(iσ2)^2=-I", Q**2 + I2)
assert_zero("tr(iσ2)=0", sp.trace(Q))
print("   scalar ±iI and traceless vector roots verified ✓")

print("§4  Multivalued logarithm as monodromy branch data")
# Spinorial half-twist example: Δ has eigenvalues ±i, so Δ^2=-I.
Delta = sp.diag(sp.I, -sp.I)
assert_matrix_zero("Delta^2=-I", Delta**2 + I2)

n1, n2 = 2, -1
log_lam1 = sp.I * (sp.pi / 2 + 2 * sp.pi * n1)      # log(i) branches
log_lam2 = sp.I * (-sp.pi / 2 + 2 * sp.pi * n2)     # log(-i) branches
Lbranch = sp.diag(log_lam1, log_lam2)
assert_matrix_zero("exp(branch log)=Delta", Lbranch.exp() - Delta)
# A different branch differs by 2πi times an integral spectral projector.
Lprincipal = sp.diag(sp.I * sp.pi / 2, -sp.I * sp.pi / 2)
branch_shift = sp.simplify(Lbranch - Lprincipal)
expected_shift = 2 * sp.pi * sp.I * sp.diag(n1, n2)
assert_matrix_zero("branch shift = 2πi integral projectors", branch_shift - expected_shift)
print("   log branches differ by 2πi projectors yet exponentiate to same monodromy ✓")

print()
print("biquaternion_negative_roots_log.py: All identities verified")
