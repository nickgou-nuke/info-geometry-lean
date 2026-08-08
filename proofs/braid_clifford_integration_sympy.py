"""SymPy witness: Artin braid skeleton meets Fibonacci/Clifford atoms.

Checks three layers:
1. Fibonacci anyon braid matrices satisfy the B3 Artin/Yang--Baxter relation
   sigma1 sigma2 sigma1 = sigma2 sigma1 sigma2.
2. The local Clifford two-atom parity channel is a square-one/tripotent
   representation of a uniform braid generator, matching the Lean bridge.
3. A nondegenerate three-atom Majorana/Clifford braid witness on an 8-dimensional
   tensor space satisfies the adjacent Artin/Yang--Baxter relation.
"""

import sympy as sp


def assert_matrix_close(name, M, tol=sp.Float("1e-40")):
    N = sp.N(M, 80)
    for entry in list(N):
        if abs(complex(entry)) > float(tol):
            raise AssertionError(f"{name} failed:\n{N}")


def assert_matrix_zero(name, M):
    S = M.applyfunc(lambda x: sp.simplify(sp.expand_func(x).rewrite(sp.exp)))
    if S != sp.zeros(*S.shape):
        raise AssertionError(f"{name} failed:\n{S}")


# --- Fibonacci anyon B3 representation ------------------------------------
phi = (1 + sp.sqrt(5)) / 2
F = sp.Matrix([[1 / phi, 1 / sp.sqrt(phi)], [1 / sp.sqrt(phi), -1 / phi]])

# Fibonacci R-symbols for tau-tau fusion channels 1 and tau.
R = sp.diag(sp.exp(-4 * sp.pi * sp.I / 5), sp.exp(3 * sp.pi * sp.I / 5))

sigma1 = R
sigma2 = sp.simplify(F * R * F)

# F is an involution, so this is the standard adjacent braid generator change of basis.
assert_matrix_zero("F^2 = I", F * F - sp.eye(2))
assert_matrix_close("Fibonacci Artin braid relation", sigma1 * sigma2 * sigma1 - sigma2 * sigma1 * sigma2)

# --- Clifford atom side -----------------------------------------------------
sigma0 = sp.eye(2)
sigma1_pauli = sp.Matrix([[0, 1], [1, 0]])
sigma2_pauli = sp.Matrix([[0, -sp.I], [sp.I, 0]])
sigma3 = sp.Matrix([[1, 0], [0, -1]])
i_sigma2 = sp.Matrix([[0, 1], [-1, 0]])
sigma_plus = sp.Matrix([[0, 1], [0, 0]])

two_atom_parity_2x2 = sigma3 * i_sigma2
P2 = sp.kronecker_product(sigma3, sigma3)
N2 = sp.kronecker_product(sigma_plus, sigma_plus)

assert_matrix_zero("twoAtomParity 2x2 equals sigma_x", two_atom_parity_2x2 - sigma1_pauli)
assert_matrix_zero("twoAtomParity 2x2 square", two_atom_parity_2x2**2 - sp.eye(2))
assert_matrix_zero("twoAtomParity 2x2 tripotent", two_atom_parity_2x2**3 - two_atom_parity_2x2)
assert_matrix_zero("iSigma2 projective cubic", i_sigma2**3 + i_sigma2)
assert_matrix_zero("two atom parity square", P2 * P2 - sp.eye(4))
assert_matrix_zero("two atom parity tripotent", P2**3 - P2)
assert_matrix_zero("two atom nilpotent square", N2 * N2)

# Degenerate uniform Clifford representation of Artin generators, matching the Lean theorem.
g0 = P2
g1 = P2
assert_matrix_zero("degenerate Clifford adjacent Artin", g0 * g1 * g0 - g1 * g0 * g1)
assert_matrix_zero("degenerate Clifford separated commutation", g0 * g1 - g1 * g0)

# --- Nondegenerate three-atom Majorana/Clifford braid witness ---------------
# Jordan-Wigner Majoranas on C^2 ⊗ C^2 ⊗ C^2.  They square to I and anticommute.
def kron(*matrices):
    out = matrices[0]
    for matrix in matrices[1:]:
        out = sp.kronecker_product(out, matrix)
    return out

majorana1 = kron(sigma1_pauli, sigma0, sigma0)
majorana2 = kron(sigma2_pauli, sigma0, sigma0)
majorana3 = kron(sigma3, sigma1_pauli, sigma0)

for idx, gamma in enumerate([majorana1, majorana2, majorana3], start=1):
    assert_matrix_zero(f"Majorana gamma{idx} square", gamma * gamma - sp.eye(8))

for (a_idx, a), (b_idx, b) in [((1, majorana1), (2, majorana2)), ((2, majorana2), (3, majorana3)), ((1, majorana1), (3, majorana3))]:
    assert_matrix_zero(f"Majorana anticomm gamma{a_idx},gamma{b_idx}", a * b + b * a)

# Braid exchange gates U_i = exp(pi/4 gamma_i gamma_{i+1}) = (I + gamma_i gamma_{i+1})/sqrt(2).
U1 = (sp.eye(8) + majorana1 * majorana2) / sp.sqrt(2)
U2 = (sp.eye(8) + majorana2 * majorana3) / sp.sqrt(2)
assert_matrix_zero("three-atom Majorana adjacent Artin/Yang-Baxter", U1 * U2 * U1 - U2 * U1 * U2)

# A separated example on three qubits: X on atom 1 commutes with X on atom 3.
sep1 = kron(sigma1_pauli, sigma0, sigma0)
sep3 = kron(sigma0, sigma0, sigma1_pauli)
assert_matrix_zero("three-atom separated commutation", sep1 * sep3 - sep3 * sep1)

# Uniform Witten amplitude is length-only, hence invariant under elementary Artin moves.
q = sp.symbols("q")
assert sp.simplify(q ** len([0, 1, 0]) - q ** len([1, 0, 1])) == 0
assert sp.simplify(q ** len([0, 2]) - q ** len([2, 0])) == 0

print("OK braid -> Fibonacci/Clifford integration SymPy witness completed")
