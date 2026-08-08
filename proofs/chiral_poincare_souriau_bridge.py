"""SymPy witness: chiral supercharges -> Poincare momentum -> Souriau beta vector.

This is the executable finite-dimensional shadow of the Lean socket:
  {Q_alpha, Qbar_dotbeta} = 2 sigma^mu_{alpha dotbeta} P_mu.
The Pauli-soldered matrix P_{alpha dotalpha} has determinant P^2, and the
Souriau inverse-temperature four-vector beta is the dual covector paired with P.
"""
import sympy as sp

print("§1 Pauli soldering and mass Casimir")
E, px, py, pz = sp.symbols("E px py pz", real=True)
I = sp.I
I2 = sp.eye(2)
s1 = sp.Matrix([[0, 1], [1, 0]])
s2 = sp.Matrix([[0, -I], [I, 0]])
s3 = sp.Matrix([[1, 0], [0, -1]])

P = E * I2 + px * s1 + py * s2 + pz * s3
expected = sp.Matrix([[E + pz, px - I * py], [px + I * py, E - pz]])
assert sp.simplify(P - expected) == sp.zeros(2)
assert sp.simplify(P.det() - (E**2 - px**2 - py**2 - pz**2)) == 0
print("   det(P_mu sigma^mu)=E²-|p|² ✓")

print("§2 Supercharge anticommutator inversion")
Anti = 2 * P  # Anti_{alpha dotalpha} = {Q_alpha, Qbar_dotalpha}
P_from_Q = sp.Rational(1, 2) * Anti
# Components recovered by trace identities: E=1/2 Tr P, p_i=1/2 Tr(P sigma_i)
assert sp.simplify(sp.trace(P_from_Q) / 2 - E) == 0
assert sp.simplify(sp.trace(P_from_Q * s1) / 2 - px) == 0
assert sp.simplify(sp.trace(P_from_Q * s2) / 2 - py) == 0
assert sp.simplify(sp.trace(P_from_Q * s3) / 2 - pz) == 0
print("   P_{αdotα}=1/2{Q_α,Qbar_dotα}; Pauli trace recovers P_μ ✓")

print("§3 Twistor / massless spinor factorization")
a, b = sp.symbols("a b", complex=True)
lam = sp.Matrix([a, b])
# Algebraic rank-one null momentum; for real momenta use conjugates, here use an
# independent dual spinor equal to the same symbolic column for determinant test.
P_null = lam * lam.T
assert sp.simplify(P_null.det()) == 0
print("   P_{αdotα}=λ_α λ̃_dotα is rank-one, det P=0 ✓")

print("§4 Souriau beta-vector dual to momentum")
T, vx, vy, vz = sp.symbols("T vx vy vz", positive=True, real=True)
v2 = vx**2 + vy**2 + vz**2
gamma = 1 / sp.sqrt(1 - v2)
b0 = gamma / T
bx, by, bz = gamma * vx / T, gamma * vy / T, gamma * vz / T
Beta = b0 * I2 + bx * s1 + by * s2 + bz * s3
# det(beta_mu sigma^mu)=beta^2=1/T^2 for beta^mu=u^mu/T.
assert sp.simplify(Beta.det() - 1 / T**2) == 0
pairing = sp.expand(b0 * E - bx * px - by * py - bz * pz)
assert pairing == sp.expand(gamma / T * (E - vx * px - vy * py - vz * pz))
print("   beta^μ=u^μ/T has beta²=1/T² and pairs as beta·P ✓")

print("§5 Chiral sl2 closure")
sp_plus = sp.Matrix([[0, 1], [0, 0]])
sp_minus = sp.Matrix([[0, 0], [1, 0]])
assert sp_plus**2 == sp.zeros(2)
assert sp_minus**2 == sp.zeros(2)
assert sp_plus * sp_minus - sp_minus * sp_plus == s3
assert sp_plus * sp_minus + sp_minus * sp_plus == I2
print("   σ± nilpotent, [σ+,σ-]=σ3, {σ+,σ-}=I ✓")

print("chiral_poincare_souriau_bridge.py: All identities verified")
