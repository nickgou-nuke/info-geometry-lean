"""Read out the ten native Cl(5,5) Pin reflection matrices.

This checks the local coordinate-reflection part of the Pin -> O map.  It is
not a proof of surjectivity onto the full orthogonal group.
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


def twisted_action(reflector, square, vector_generator):
    return -(reflector * vector_generator * (reflector / square))


def action_matrix(reflector, square):
    columns = [coordinates(twisted_action(reflector, square, X))
               for X in clifford_vectors]
    return matrix(Q, 10, 10, lambda r, c: columns[c][r])


reports = []
for index, (reflector, square) in enumerate(
        zip(clifford_vectors, clifford_squares)):
    action = action_matrix(reflector, square)
    expected = identity_matrix(Q, 10)
    expected[index, index] = -1
    reports.append({
        "label": "gamma%d" % index,
        "square": square,
        "is_coordinate_reflection": action == expected,
        "is_involution": action * action == identity_matrix(Q, 10),
        "preserves_quadratic_form":
            action.transpose() * quadratic_form * action == quadratic_form,
        "axis": index,
    })

assert all(report["is_coordinate_reflection"] for report in reports)
assert all(report["is_involution"] for report in reports)
assert all(report["preserves_quadratic_form"] for report in reports)

report = {
    "coefficient_field": "QQ",
    "clifford_signature": [5, 5],
    "clifford_generator_count": 10,
    "pin_cover_target": "Pin(5,5) -> O(5,5)",
    "twisted_adjoint_checked": True,
    "coordinate_reflections_checked": 10,
    "all_coordinate_reflections_verified": True,
    "full_orthogonal_surjectivity_proved": False,
    "weyl_quotient_identified": False,
    "reflections": reports,
}

export_path = (
    "tools/experiments/cl55_five_grade/export/"
    "pin_coordinate_reflections.json")
with open(export_path, "w") as stream:
    json.dump(report, stream, indent=2, sort_keys=True, default=int)

print("SAGE:pin_cover_target=Pin(5,5)->O(5,5)")
print("SAGE:coordinate_reflections_checked=10")
print("SAGE:all_coordinate_reflections_verified=true")
print("SAGE:full_orthogonal_surjectivity_proved=false")
print("SAGE:reflection_report=%s" % export_path)
