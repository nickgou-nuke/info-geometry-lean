#!/usr/bin/env sage
"""Exact CAS check for the Zorn/Jordan-Wigner basis-change matrix.

Lean owners:
  - InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone.zornMul,
    embedVec, fin8ToZorn, zornToFin8
  - InfoGeometry.Canonical.SplitOctonionClifford33Soldering.zornLeftActMatrix
  - InfoGeometry.Canonical.MajoranaEightByEightJW.majoranaGenZ

Carrier alignment: vectors are column coordinates indexed by Fin 8 in occupation
order 0,...,7. The Fock chart is exactly (a,u0,u1,u2,v0,v1,v2,b) =
(psi0,psi4,psi2,psi1,psi3,-psi5,psi6,psi7), copied from fin8ToZorn and
zornToFin8. Zorn multiplication below uses the owner formula, including the
cross-product orientation in vec3Cross. Clifford generator order is Fin 6:
mode 0 plus/minus, mode 1 plus/minus, mode 2 plus/minus, from the six
Jordan-Wigner tensor strings documented by MajoranaEightByEightJW.

The checked identity is L_k S = S Gamma_k, where S swaps the 0th and 7th
occupation coordinates and fixes 1,...,6. Thus L_k = S Gamma_k S since S^2=I.
This is a finite exact-arithmetic check; Lean kernel proofs remain authoritative.
"""

import json
from pathlib import Path

from sage.all import ZZ, QQ, identity_matrix, diagonal_matrix, matrix, vector


def kron(left, right):
    return left.tensor_product(right)


I2 = identity_matrix(ZZ, 2)
Z = diagonal_matrix(ZZ, [1, -1])
X = matrix(ZZ, [[0, 1], [1, 0]])
E = matrix(ZZ, [[0, -1], [1, 0]])
gammas = [
    kron(kron(X, I2), I2),
    kron(kron(E, I2), I2),
    kron(kron(Z, X), I2),
    kron(kron(Z, E), I2),
    kron(kron(Z, Z), X),
    kron(kron(Z, Z), E),
]


def dot(left, right):
    return sum(left[k] * right[k] for k in range(3))


def cross(left, right):
    return vector(
        ZZ,
        [
            left[1] * right[2] - left[2] * right[1],
            left[2] * right[0] - left[0] * right[2],
            left[0] * right[1] - left[1] * right[0],
        ],
    )


def fin8_to_zorn(psi):
    return vector(ZZ, [psi[0], psi[4], psi[2], psi[1], psi[3], -psi[5], psi[6], psi[7]])


def zorn_to_fin8(value):
    return vector(ZZ, [value[0], value[3], value[2], value[4], value[1], -value[5], value[6], value[7]])


def zorn_mul(left, right):
    a, u, v, b = left[0], left[1:4], left[4:7], left[7]
    c, p, q, d = right[0], right[1:4], right[4:7], right[7]
    return vector(
        ZZ,
        [dot(u, q)]
        + [d * u[k] - cross(v, q)[k] for k in range(3)]
        + [c * v[k] + cross(u, p)[k] for k in range(3)]
        + [dot(v, p)],
    )


def left_action_matrix(u, v):
    columns = []
    x = vector(ZZ, [0, *u, *v, 0])
    for column in range(8):
        psi = vector(ZZ, [int(index == column) for index in range(8)])
        columns.append(zorn_to_fin8(zorn_mul(x, fin8_to_zorn(psi))))
    return matrix(ZZ, 8, 8, lambda row, col: columns[col][row])


left_actions = []
for mode in range(3):
    basis = vector(ZZ, [int(index == mode) for index in range(3)])
    left_actions.extend([left_action_matrix(basis, basis), left_action_matrix(basis, -basis)])

swap = matrix(ZZ, 8, 8, lambda row, col: int((row == 7 and col == 0) or (row == 0 and col == 7) or (row == col and row not in (0, 7))))
assert swap * swap == identity_matrix(ZZ, 8)
assert all(left * swap == swap * gamma for left, gamma in zip(left_actions, gammas))
assert all(left * left == ((-1) ** (index % 2)) * identity_matrix(ZZ, 8) for index, left in enumerate(left_actions))

# Solve the homogeneous linear system for an arbitrary 8x8 intertwiner T:
#     L_k T - T Gamma_k = 0, for each of the six generators.
# Variables are T[a,b], in row-major order. This verifies the recorded nullity
# rather than copying a claimed dimension into the output artifact.
constraint_rows = []
for left, gamma in zip(left_actions, gammas):
    for row in range(8):
        for col in range(8):
            coefficients = [ZZ(0)] * 64
            for a in range(8):
                coefficients[8 * a + col] += left[row, a]
            for b in range(8):
                coefficients[8 * row + b] -= gamma[b, col]
            constraint_rows.append(coefficients)
intertwiner_constraints = matrix(QQ, constraint_rows)
intertwiner_kernel_dimension = 64 - intertwiner_constraints.rank()
assert intertwiner_kernel_dimension == 1
determinant_swap = swap.det()
assert determinant_swap == -1

# Mandatory carrier round trip on a non-basis vector, for mode 1's positive generator.
sample = vector(ZZ, [2, -3, 5, 7, 11, -13, 17, 19])
mode1_basis = vector(ZZ, [0, 1, 0])
zorn_applied = zorn_to_fin8(
    zorn_mul(vector(ZZ, [0, *mode1_basis, *mode1_basis, 0]), fin8_to_zorn(sample))
)
matrix_applied = left_actions[2] * sample
assert zorn_applied == matrix_applied
assert left_actions[2] * (swap * sample) == swap * (gammas[2] * sample)

artifact = {
    "object": "zorn_left_action_jordan_wigner_intertwiner",
    "lean_owners": [
        "InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone",
        "InfoGeometry.Canonical.SplitOctonionClifford33Soldering",
        "InfoGeometry.Canonical.MajoranaEightByEightJW",
    ],
    "carrier": "Fin 8 -> ZornSplitOctonion Z; integer coordinate matrices indexed by Fin 8",
    "basis_order": ["000", "001", "010", "011", "100", "101", "110", "111"],
    "fock_chart": "(a,u0,u1,u2,v0,v1,v2,b)=(psi0,psi4,psi2,psi1,psi3,-psi5,psi6,psi7)",
    "generator_order": ["mode0+", "mode0-", "mode1+", "mode1-", "mode2+", "mode2-"],
    "multiplication_convention": "owner zornMul; column action y -> x star y",
    "matrix_convention": "column coordinates; Matrix row i, column j is output coordinate i on input basis vector j",
    "intertwiner": "S swaps Fin 8 coordinates 0 and 7, and fixes 1,...,6",
    "identity_checked": "L_k * S = S * Gamma_k for all six generators; S^2=I",
    "round_trip_verified": True,
    "round_trip_element": [int(value) for value in sample],
    "round_trip_generator": "mode1+",
    "kernel_dimension_of_intertwiner_space": int(intertwiner_kernel_dimension),
    "kernel_computation_field": "QQ",
    "determinant_S": int(determinant_swap),
    "checked": True,
    "scope_limit": "Exact finite matrix equivalence only; no universal Clifford algebra isomorphism is certified by this CAS artifact.",
    "S_rows": [[int(entry) for entry in row] for row in swap.rows()],
}
encoded = json.dumps(artifact, indent=2, default=lambda value: value.__int__()) + "\n"
Path("scripts/zorn_jw_intertwiner.json").write_text(encoded)
print(encoded)
