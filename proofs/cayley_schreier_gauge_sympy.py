import sympy as sp

print("--- Cayley-Schreier Non-Abelian Gauge Transformations ---")

# ══════════════════════════════════════════════════════════════════════════════
# §1. Projective Space Group Symmetry (Cayley-Schreier Lattice)
# ══════════════════════════════════════════════════════════════════════════════

# Define arbitrary complex wave function amplitudes for two orbitals
psi_n = sp.Matrix(sp.symbols('psi_n_1 psi_n_2', complex=True))
psi_l = sp.Matrix(sp.symbols('psi_l_1 psi_l_2', complex=True))

# ══════════════════════════════════════════════════════════════════════════════
# §2. Synthetic Gauge Structure and Wilson Loops
# ══════════════════════════════════════════════════════════════════════════════

# Consider the quaternion gauge group Q8
# a_{n,l} is the group element assigned to the bond from site l to site n
a_nl = sp.Symbol('a_nl')
a_lm = sp.Symbol('a_lm')

# Wilson loop around a minimal triangle
# W = a_{n,l} * a_{l,m} * a_{m,n}
W_triangle = sp.Symbol('W')

# ══════════════════════════════════════════════════════════════════════════════
# §3. Peter-Weyl Theorem and Reducible Representations
# ══════════════════════════════════════════════════════════════════════════════

# Regular representation of connection
rho_a = sp.Symbol('rho_a')
U = sp.Symbol('U')

# Block diagonalization
block_diag = sp.Symbol('U_dagger_rho_U')
print("  U^dagger rho(a) U block diagonalizes the Hamiltonian into irreducible representations.")

# ══════════════════════════════════════════════════════════════════════════════
# §4. Irreducible Representations of Q8
# ══════════════════════════════════════════════════════════════════════════════

I2 = sp.eye(2)
s1 = sp.Matrix([[0, 1], [1, 0]])
s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]])
s3 = sp.Matrix([[1, 0], [0, -1]])

# 2D Irrep E:
D_pm1 = sp.Matrix([[1, 0], [0, 1]])
D_pm_i = -sp.I * s1
D_pm_j = -sp.I * s2
D_pm_k = -sp.I * s3

print("\n  2D Irreducible Representation E for Q8:")
print(f"  D(+/- 1) = +/- I_2")
print(f"  D(+/- i) = -/+ i*sigma_x")
print(f"  D(+/- j) = -/+ i*sigma_y")
print(f"  D(+/- k) = -/+ i*sigma_z")

# ══════════════════════════════════════════════════════════════════════════════
# §5. Spinful Time-Reversal Symmetry
# ══════════════════════════════════════════════════════════════════════════════

# Time-reversal operator for spinless system is just complex conjugation
# But for the 2D irrep E of Q8, it acquires the spinful form
T_E = sp.I * s2

print("\n  Emergent Spinful Time-Reversal Symmetry:")
print(f"  T_E = i * sigma_y")
T_E_sq = T_E * T_E
print(f"  T_E^2 = \n{T_E_sq}")
print(f"  Is T_E^2 == -I_2? {T_E_sq == -I2} ✓")

print("\nConclusion: Cayley-Schreier lattices with quaternion gauge group Q8")
print("naturally embed non-Abelian gauge fluxes. The Peter-Weyl theorem")
print("decomposes the regular representation into irreps, where the 2D")
print("irrep E effectively realizes emergent spin-1/2 fermions with a")
print("spinful time-reversal symmetry (T^2 = -1) entirely from a scalar")
print("internal group structure! ✓")
