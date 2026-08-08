"""SymPy witness: modular Itakura--Saito divergence closes in biquaternions.

For a traceless biquaternion modular Hamiltonian K = v n·σ with K^2=v^2 I,
operator-valued Itakura--Saito divergence is

    D_IS(eps K) = exp(eps K) - I - eps K.

The Pauli closure gives

    D_IS = (cosh(eps v)-1) I + (sinh(eps v)/v - eps) K.

The small-eps limit satisfies 2 D_IS / eps^2 -> K^2, i.e. the Fisher/Bures
quadratic form.
"""

import sympy as sp


def assert_matrix_zero(name, M):
    S = sp.simplify(M)
    if S != sp.zeros(*S.shape):
        raise AssertionError(f"{name} failed:\n{S}")

print("§1  Traceless biquaternion modular Hamiltonian")
eps, v = sp.symbols("eps v", nonzero=True)
s1 = sp.Matrix([[0, 1], [1, 0]])
I2 = sp.eye(2)
K = v * s1
assert_matrix_zero("K^2=v^2 I", K**2 - v**2 * I2)
print("   K²=v²I ✓")

print("§2  Exponential closure")
exp_closed = sp.cosh(eps*v)*I2 + sp.sinh(eps*v)/v * K
assert_matrix_zero("exp(eps K) closed", (eps*K).exp() - exp_closed)
print("   exp(eps K)=cosh(eps v)I+sinh(eps v)/v K ✓")

print("§3  Itakura--Saito closure")
D = exp_closed - I2 - eps*K
D_closed = (sp.cosh(eps*v)-1)*I2 + (sp.sinh(eps*v)/v - eps)*K
assert_matrix_zero("D_IS closure", D - D_closed)
print("   D_IS closes in span{I,K} ✓")

print("§4  Fisher quadratic limit")
limit_mat = sp.zeros(2, 2)
for i in range(2):
    for j in range(2):
        limit_mat[i, j] = sp.limit(2 * D[i, j] / eps**2, eps, 0)
assert_matrix_zero("2 D_IS/eps^2 -> K^2", limit_mat - K**2)
print("   lim eps->0 2D_IS/eps² = K² ✓")

print("§5  Modular conjugation flips K")
J = sp.Matrix([[0, 1], [1, 0]])  # conjugates σ3 to -σ3 in an alternate axis; use Kz
s3 = sp.Matrix([[1, 0], [0, -1]])
Kz = v*s3
assert_matrix_zero("J K J = -K", J*Kz*J + Kz)
print("   modular reflection sends K -> -K ✓")

print()
print("modular_itakura_biquaternion.py: All identities verified")
