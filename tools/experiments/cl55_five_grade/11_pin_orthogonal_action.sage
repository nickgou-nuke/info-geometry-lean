"""Exact Pin/O(5,5) action checks for the Cl(5,5) Witt packet.

This is computational evidence only.  Clifford vectors act on the ten
dimensional quadratic space by the twisted adjoint action

    alpha_v(x) = -v*x*v^(-1).

The script records the induced orthogonal matrices separately from the
spinor-carrier operators and does not claim a formal Pin group theorem.
"""

load("tools/experiments/cl55_five_grade/01_cl55_witt_generators.sage")
import json


def flat_vector(M):
    return vector(Q, [M[r, c] for r in range(32) for c in range(32)])


clifford_vectors = positive_gamma + negative_gamma
clifford_squares = [1] * 5 + [-1] * 5
clifford_matrix = matrix(Q, 1024, 10,
                         lambda r, j: clifford_vectors[j][r // 32, r % 32])
assert clifford_matrix.rank() == 10

quadratic_form = diagonal_matrix(Q, clifford_squares)


def vector_coordinates(M):
    return clifford_matrix.solve_right(flat_vector(M))


def induced_matrix(operator, twisted=False, square=1):
    columns = []
    for vector_generator in clifford_vectors:
        inverse = operator / square
        image = operator * vector_generator * inverse
        if twisted:
            image = -image
        columns.append(vector_coordinates(image))
    return matrix(Q, 10, 10, lambda r, c: columns[c][r])


def orthogonal_report(label, operator, square, twisted):
    action = induced_matrix(operator, twisted=twisted, square=square)
    return {
        "label": label,
        "operator_square": square,
        "action_kind": "twisted_adjoint" if twisted else "adjoint",
        "action_square_is_identity": action * action == identity_matrix(Q, 10),
        "preserves_quadratic_form":
            action.transpose() * quadratic_form * action == quadratic_form,
        "action_matrix": [[int(action[r, c]) for c in range(10)]
                          for r in range(10)],
    }


reports = []
for index, (reflector, square) in enumerate(
        zip(clifford_vectors, clifford_squares)):
    reports.append(orthogonal_report(
        "gamma%d" % index, reflector, square, twisted=True))

volume = ordered_product(clifford_vectors)
volume_square = volume * volume
assert volume_square in [Id, -Id]
reports.append(orthogonal_report(
    "volume", volume, 1 if volume_square == Id else -1, twisted=True))


def mode_bit(i):
    return 1 << (4 - i)


def permutation_lift(permutation):
    U = zero_matrix(Q, 32)
    for mask in range(32):
        selected = [i for i in range(5) if mask & mode_bit(i)]
        target = sum(mode_bit(permutation[i]) for i in selected)
        inversions = sum(
            permutation[i] > permutation[j]
            for position, i in enumerate(selected)
            for j in selected[position + 1:])
        U[target, mask] = (-1) ** inversions
    return U


for i in range(4):
    permutation = list(range(5))
    permutation[i], permutation[i + 1] = permutation[i + 1], permutation[i]
    U = permutation_lift(permutation)
    reports.append(orthogonal_report(
        "mode_swap_%d_%d" % (i, i + 1), U, 1, twisted=False))

sign_lift = positive_gamma[0] * negative_gamma[0]
reports.append(orthogonal_report("mode_sign_0", sign_lift, 1, twisted=False))

assert all(report["preserves_quadratic_form"] for report in reports)

report = {
    "coefficient_field": "QQ",
    "spinor_dimension": 32,
    "clifford_vector_dimension": 10,
    "clifford_signature": [5, 5],
    "pin_to_orthogonal_map": "twisted_adjoint",
    "pin_vector_reflections_checked": 10,
    "orthogonal_actions_checked": len(reports),
    "all_actions_preserve_quadratic_form": True,
    "all_reported_actions_are_involutions": all(
        report["action_square_is_identity"] for report in reports),
    "weyl_group_order": 3840,
    "weyl_group_identified_in_separate_report": True,
    "pin_group_extension_proved": False,
    "reports": reports,
}

export_path = "tools/experiments/cl55_five_grade/export/pin_orthogonal_action.json"
with open(export_path, "w") as stream:
    json.dump(report, stream, indent=2, sort_keys=True, default=int)

print("SAGE:pin_vector_reflections_checked=10")
print("SAGE:orthogonal_actions_checked=%d" % len(reports))
print("SAGE:all_actions_preserve_quadratic_form=true")
print("SAGE:weyl_group_order=3840")
print("SAGE:pin_report=%s" % export_path)
