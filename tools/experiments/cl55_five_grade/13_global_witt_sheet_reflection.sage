"""Global particle-hole/Witt-sheet reflection for the Cl(5,5) packet.

The odd Clifford versor J = Gamma_0^+ ... Gamma_4^+ exchanges creation and
annihilation operators.  This is an exact finite-dimensional check of its
induced O(5,5) reflection; it is not a formal Pin-cover theorem.
"""

load("tools/experiments/cl55_five_grade/01_cl55_witt_generators.sage")
import json

clifford_vectors = positive_gamma + negative_gamma
clifford_squares = [1] * 5 + [-1] * 5
clifford_matrix = matrix(
    Q, 1024, 10,
    lambda r, j: clifford_vectors[j][r // 32, r % 32])
quadratic_form = diagonal_matrix(Q, clifford_squares)


def coordinates(M):
    return clifford_matrix.solve_right(
        vector(Q, [M[r, c] for r in range(32) for c in range(32)]))


def flat(M):
    return vector(Q, [M[r, c] for r in range(32) for c in range(32)])


def in_lie_span(M):
    return matrix(Q, [flat(X) for X in lie_basis] + [flat(M)]).rank() == 55


J = ordered_product(positive_gamma)
assert J * J == Id
assert all(J * creators[i] * J == annihilators[i] for i in range(5))
assert all(J * annihilators[i] * J == creators[i] for i in range(5))
assert J * N * J == -N

columns = [coordinates(J * X * J) for X in clifford_vectors]
orthogonal_action = matrix(Q, 10, 10,
                           lambda r, c: columns[c][r])
expected_action = block_matrix(Q, 2, 2, [identity_matrix(Q, 5),
                                          zero_matrix(Q, 5),
                                          zero_matrix(Q, 5),
                                          -identity_matrix(Q, 5)])

assert orthogonal_action == expected_action
assert orthogonal_action.transpose() * quadratic_form * orthogonal_action == quadratic_form
assert orthogonal_action * orthogonal_action == identity_matrix(Q, 10)
assert orthogonal_action.det() == -1

grade_reversal = all(in_lie_span(J * X * J) for X in lie_basis)
assert grade_reversal

report = {
    "coefficient_field": "QQ",
    "carrier_dimension": 32,
    "clifford_signature": [5, 5],
    "pin_cover_target": "Pin(5,5) -> O(5,5)",
    "versor": "Gamma_0^+ Gamma_1^+ Gamma_2^+ Gamma_3^+ Gamma_4^+",
    "versor_parity": "odd",
    "raw_pin_square": 1,
    "induced_action_square": 1,
    "induced_action_determinant": -1,
    "preserves_quadratic_form": True,
    "exchanges_creation_annihilation": True,
    "reverses_N": True,
    "reverses_witt_grades": True,
    "full_pin_cover_proved": False,
    "full_orthogonal_surjectivity_proved": False,
    "orthogonal_action_matrix": [
        [int(orthogonal_action[r, c]) for c in range(10)]
        for r in range(10)],
}

export_path = (
    "tools/experiments/cl55_five_grade/export/"
    "global_witt_sheet_reflection.json")
with open(export_path, "w") as stream:
    json.dump(report, stream, indent=2, sort_keys=True, default=int)

print("SAGE:global_sheet_reflection=verified")
print("SAGE:raw_pin_square=1")
print("SAGE:induced_action_determinant=-1")
print("SAGE:exchanges_creation_annihilation=true")
print("SAGE:reverses_N=true")
print("SAGE:reflection_report=%s" % export_path)
