import sympy as sp
from sympy import Matrix, eye, zeros, kronecker_product

# 2x2 local operator basis
I2 = eye(2)
X = Matrix([[0, 1], [1, 0]])
Z = Matrix([[1, 0], [0, -1]])
J = Matrix([[0, 1], [-1, 0]])   # real form of iY, so J^2 = -I and XJ = -JX = -Z
P0 = Matrix([[1, 0], [0, 0]])
P1 = Matrix([[0, 0], [0, 1]])
Sp = Matrix([[0, 1], [0, 0]])   # |0><1| = (X + J)/2
Sm = Matrix([[0, 0], [1, 0]])   # |1><0| = (X - J)/2


def matrix_units_4():
    out = {}
    for i in range(4):
        for j in range(4):
            m = zeros(4)
            m[i, j] = 1
            out[(i, j)] = m
    return out


def superbracket(a: Matrix, b: Matrix, parity_a: int, parity_b: int) -> Matrix:
    if parity_a == 1 and parity_b == 1:
        return a * b + b * a
    return a * b - b * a


E = matrix_units_4()

# 3x3 operator-first witnesses matching the Lean operator surface discussion.
I3 = eye(3)
I2_small = eye(2)
T3 = sp.diag(1, 0, -1)
P_vac3 = I3 - T3**2
P_up3 = (T3**2 + T3) / 2
P_down3 = (T3**2 - T3) / 2
E12_3 = Matrix([[0, 1, 0], [0, 0, 0], [0, 0, 0]])
E21_3 = Matrix([[0, 0, 0], [1, 0, 0], [0, 0, 0]])
E12_2 = Matrix([[0, 1], [0, 0]])
E21_2 = Matrix([[0, 0], [1, 0]])
Gamma3 = sp.diag(1, 1, -1)
S_active3 = E12_3 * E21_3 + E21_3 * E12_3
Compress12 = Matrix([[1, 0], [0, 1], [0, 0]])

def grade_conjugation_even_part(gamma: Matrix, a: Matrix) -> Matrix:
    return (a + gamma * a * gamma) / 2

def grade_conjugation_odd_part(gamma: Matrix, a: Matrix) -> Matrix:
    return (a - gamma * a * gamma) / 2

# Use the three-state subspace {00, 01, 10} inside two qubits.
H4 = E[(0, 0)] - E[(1, 1)]
Ep4 = E[(0, 1)]
Em4 = E[(1, 0)]
G14 = E[(0, 2)] + E[(2, 1)]
G24 = E[(1, 2)] - E[(2, 0)]

# Explicit local formulas built from projector/tripotent/nilpotent pieces.
H4_formula = kronecker_product(P0, Z)
Ep4_formula = kronecker_product(P0, Sp)
Em4_formula = kronecker_product(P0, Sm)
G14_formula = kronecker_product(Sp, P0) + kronecker_product(Sm, Sp)
G24_formula = kronecker_product(Sp, Sm) - kronecker_product(Sm, P0)

# The same formulas rewritten in a Pauli/real-Clifford basis.
# Here P0 = (I + Z)/2, Sp = (X + J)/2, Sm = (X - J)/2 with J^2 = -I and XJ = -JX.
H4_pauli = (kronecker_product(I2, Z) + kronecker_product(Z, Z)) / 2
Ep4_pauli = (
    kronecker_product(I2, X) + kronecker_product(I2, J)
    + kronecker_product(Z, X) + kronecker_product(Z, J)
) / 4
Em4_pauli = (
    kronecker_product(I2, X) - kronecker_product(I2, J)
    + kronecker_product(Z, X) - kronecker_product(Z, J)
) / 4
G14_pauli = (
    kronecker_product(X, I2) + kronecker_product(X, X)
    + kronecker_product(X, J) + kronecker_product(X, Z)
    + kronecker_product(J, I2) - kronecker_product(J, X)
    - kronecker_product(J, J) + kronecker_product(J, Z)
) / 4
G24_pauli = (
    -kronecker_product(X, I2) + kronecker_product(X, X)
    - kronecker_product(X, J) - kronecker_product(X, Z)
    + kronecker_product(J, I2) + kronecker_product(J, X)
    - kronecker_product(J, J) + kronecker_product(J, Z)
) / 4

# Extend from 4x4 to 32x32 by tensoring identity on the remaining 3 qubits.
I8 = eye(8)

def ext(a: Matrix) -> Matrix:
    return kronecker_product(a, I8)

H = ext(H4)
Ep = ext(Ep4)
Em = ext(Em4)
G1 = ext(G14)
G2 = ext(G24)
P3 = ext(E[(0, 0)] + E[(1, 1)] + E[(2, 2)])
Z1 = ext(kronecker_product(Z, I2))

checks = {
    "T3^3 = T3": (T3**3 - T3).equals(zeros(3)),
    "T3^2 = P_up + P_down": (T3**2 - (P_up3 + P_down3)).equals(zeros(3)),
    "P_vac^2 = P_vac": (P_vac3**2 - P_vac3).equals(zeros(3)),
    "P_up^2 = P_up": (P_up3**2 - P_up3).equals(zeros(3)),
    "P_down^2 = P_down": (P_down3**2 - P_down3).equals(zeros(3)),
    "P_vac P_up = 0": (P_vac3 * P_up3).equals(zeros(3)),
    "P_vac P_down = 0": (P_vac3 * P_down3).equals(zeros(3)),
    "P_up P_down = 0": (P_up3 * P_down3).equals(zeros(3)),
    "P_vac + P_up + P_down = I": (P_vac3 + P_up3 + P_down3 - I3).equals(zeros(3)),
    "E12^2 = 0": (E12_3**2).equals(zeros(3)),
    "E21^2 = 0": (E21_3**2).equals(zeros(3)),
    "E12E21 + E21E12 = diag(1,1,0)": (S_active3 - sp.diag(1, 1, 0)).equals(zeros(3)),
    "active support is projector": (S_active3**2 - S_active3).equals(zeros(3)),
    "E12 supported on active projector": (S_active3 * E12_3 - E12_3).equals(zeros(3)) and (E12_3 * S_active3 - E12_3).equals(zeros(3)),
    "E21 supported on active projector": (S_active3 * E21_3 - E21_3).equals(zeros(3)) and (E21_3 * S_active3 - E21_3).equals(zeros(3)),
    "2x2 null pair anticommutator = I": (E12_2 * E21_2 + E21_2 * E12_2 - I2_small).equals(zeros(2)),
    "compress E12_3 to E12_2": (Compress12.T * E12_3 * Compress12 - E12_2).equals(zeros(2)),
    "compress E21_3 to E21_2": (Compress12.T * E21_3 * Compress12 - E21_2).equals(zeros(2)),
    "compress active support to I2": (Compress12.T * S_active3 * Compress12 - I2_small).equals(zeros(2)),
    "Gamma^2 = I": (Gamma3**2 - I3).equals(zeros(3)),
    "H4 is Gamma-even": (Gamma3 * H4[:3,:3] - H4[:3,:3] * Gamma3).equals(zeros(3)),
    "Ep4 is Gamma-even": (Gamma3 * Ep4[:3,:3] - Ep4[:3,:3] * Gamma3).equals(zeros(3)),
    "Em4 is Gamma-even": (Gamma3 * Em4[:3,:3] - Em4[:3,:3] * Gamma3).equals(zeros(3)),
    "G14 is Gamma-odd": (Gamma3 * G14[:3,:3] + G14[:3,:3] * Gamma3).equals(zeros(3)),
    "G24 is Gamma-odd": (Gamma3 * G24[:3,:3] + G24[:3,:3] * Gamma3).equals(zeros(3)),
    "even+odd recovers G14": (
        grade_conjugation_even_part(Gamma3, G14[:3,:3])
        + grade_conjugation_odd_part(Gamma3, G14[:3,:3])
        - G14[:3,:3]
    ).equals(zeros(3)),
    "Sp = (X + J)/2": (Sp - (X + J) / 2).equals(zeros(2)),
    "Sm = (X - J)/2": (Sm - (X - J) / 2).equals(zeros(2)),
    "J^2 = -I": (J**2 + I2).equals(zeros(2)),
    "XZ + ZX = 0": (X*Z + Z*X).equals(zeros(2)),
    "XJ + JX = 0": (X*J + J*X).equals(zeros(2)),
    "ZJ + JZ = 0": (Z*J + J*Z).equals(zeros(2)),
    "H4 formula": (H4_formula - H4).equals(zeros(4)),
    "Ep4 formula": (Ep4_formula - Ep4).equals(zeros(4)),
    "Em4 formula": (Em4_formula - Em4).equals(zeros(4)),
    "G14 formula": (G14_formula - G14).equals(zeros(4)),
    "G24 formula": (G24_formula - G24).equals(zeros(4)),
    "H4 pauli": (H4_pauli - H4).equals(zeros(4)),
    "Ep4 pauli": (Ep4_pauli - Ep4).equals(zeros(4)),
    "Em4 pauli": (Em4_pauli - Em4).equals(zeros(4)),
    "G14 pauli": (G14_pauli - G14).equals(zeros(4)),
    "G24 pauli": (G24_pauli - G24).equals(zeros(4)),
    "H^3 = H": (H**3 - H).equals(zeros(32)),
    "P3^3 = P3": (P3**3 - P3).equals(zeros(32)),
    "Z1^3 = Z1": (Z1**3 - Z1).equals(zeros(32)),
    "[H,Ep] = 2 Ep": (superbracket(H, Ep, 0, 0) - 2 * Ep).equals(zeros(32)),
    "[H,Em] = -2 Em": (superbracket(H, Em, 0, 0) + 2 * Em).equals(zeros(32)),
    "[Ep,Em] = H": (superbracket(Ep, Em, 0, 0) - H).equals(zeros(32)),
    "[H,G1] = G1": (superbracket(H, G1, 0, 1) - G1).equals(zeros(32)),
    "[H,G2] = -G2": (superbracket(H, G2, 0, 1) + G2).equals(zeros(32)),
    "[Ep,G2] = G1": (superbracket(Ep, G2, 0, 1) - G1).equals(zeros(32)),
    "[Em,G1] = G2": (superbracket(Em, G1, 0, 1) - G2).equals(zeros(32)),
    "[G1,G1] = 2 Ep": (superbracket(G1, G1, 1, 1) - 2 * Ep).equals(zeros(32)),
    "[G2,G2] = -2 Em": (superbracket(G2, G2, 1, 1) + 2 * Em).equals(zeros(32)),
    "[G1,G2] = -H": (superbracket(G1, G2, 1, 1) + H).equals(zeros(32)),
    "[G2,G1] = -H": (superbracket(G2, G1, 1, 1) + H).equals(zeros(32)),
}

vecs = [sp.Matrix(a).reshape(32 * 32, 1) for a in [H, Ep, Em, G1, G2]]
rank = sp.Matrix.hstack(*vecs).rank()

print("Tripotent/projector/operator-surface checks:")
for key in [
    "T3^3 = T3",
    "T3^2 = P_up + P_down",
    "P_vac^2 = P_vac", "P_up^2 = P_up", "P_down^2 = P_down",
    "P_vac P_up = 0", "P_vac P_down = 0", "P_up P_down = 0",
    "P_vac + P_up + P_down = I",
    "E12^2 = 0", "E21^2 = 0", "E12E21 + E21E12 = diag(1,1,0)",
    "active support is projector",
    "E12 supported on active projector", "E21 supported on active projector",
    "2x2 null pair anticommutator = I",
    "compress E12_3 to E12_2", "compress E21_3 to E21_2",
    "compress active support to I2",
    "Gamma^2 = I",
    "H4 is Gamma-even", "Ep4 is Gamma-even", "Em4 is Gamma-even",
    "G14 is Gamma-odd", "G24 is Gamma-odd",
    "even+odd recovers G14",
    "Sp = (X + J)/2", "Sm = (X - J)/2", "J^2 = -I",
    "XZ + ZX = 0", "XJ + JX = 0", "ZJ + JZ = 0",
    "H4 formula", "Ep4 formula", "Em4 formula", "G14 formula", "G24 formula",
    "H4 pauli", "Ep4 pauli", "Em4 pauli", "G14 pauli", "G24 pauli",
    "H^3 = H", "P3^3 = P3", "Z1^3 = Z1"
]:
    print(f"  {key}: {checks[key]}")

print("\nOperator-first 3x3 witnesses:")
print("  T3 = diag(1,0,-1)")
print("  P_vac = I - T3^2")
print("  P_up  = (T3^2 + T3)/2")
print("  P_down = (T3^2 - T3)/2")
print("  T3^2 = P_up + P_down = diag(1,0,1)")
print("  Gamma3 = diag(1,1,-1)")
print("  E12 = |1><2|, E21 = |2><1| on the 3x3 carrier")
print("  active null-pair support S = {E12,E21} = diag(1,1,0)")
print("  this script keeps T3^2 and the active support S distinct")
print("  compressing the active support block recovers the intrinsic 2x2 null-pair picture")

print("\nRefined explicit ambient formulas on the 2-qubit core:")
print("  H4  = (I⊗Z + Z⊗Z)/2")
print("  Ep4 = (I⊗X + I⊗J + Z⊗X + Z⊗J)/4")
print("  Em4 = (I⊗X - I⊗J + Z⊗X - Z⊗J)/4")
print("  G14 = (X⊗I + X⊗X + X⊗J + X⊗Z + J⊗I - J⊗X - J⊗J + J⊗Z)/4")
print("  G24 = (-X⊗I + X⊗X - X⊗J - X⊗Z + J⊗I + J⊗X - J⊗J + J⊗Z)/4")
print("  ambient lift: Hc = H4⊗I8, Epc = Ep4⊗I8, Emc = Em4⊗I8, G1c = G14⊗I8, G2c = G24⊗I8")

print("\nAuthentic osp(1|2) bracket-table checks in the 32x32 ambient operator representation:")
for key in [
    "[H,Ep] = 2 Ep",
    "[H,Em] = -2 Em",
    "[Ep,Em] = H",
    "[H,G1] = G1",
    "[H,G2] = -G2",
    "[Ep,G2] = G1",
    "[Em,G1] = G2",
    "[G1,G1] = 2 Ep",
    "[G2,G2] = -2 Em",
    "[G1,G2] = -H",
    "[G2,G1] = -H",
]:
    print(f"  {key}: {checks[key]}")

print(f"\nLinear independence rank of [H, Ep, Em, G1, G2]: {rank}")
print(f"OVERALL: {all(checks.values()) and rank == 5}")
