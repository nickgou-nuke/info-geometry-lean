"""Exact Pin(5,5) reflection checks for the Witt spinor model.

The report separates the twisted adjoint action on the ten-dimensional
quadratic carrier from ordinary conjugation on the 32-dimensional spinor
carrier.  It is an experimental certificate, not a Pin covering theorem.
"""

import json

Q = QQ
I2 = identity_matrix(Q, 2)
X = matrix(Q, [[0, 1], [1, 0]])
Z = matrix(Q, [[1, 0], [0, -1]])
C = matrix(Q, [[0, 1], [-1, 0]])
R = (X + C) / 2
A = (X - C) / 2
Id = identity_matrix(Q, 32)


def jw(factors):
    result = factors[0]
    for factor in factors[1:]:
        result = result.tensor_product(factor)
    return result


creators = []
annihilators = []
positive_gamma = []
negative_gamma = []
for i in range(5):
    prefix = [Z] * i
    suffix = [I2] * (4 - i)
    creators.append(jw(prefix + [R] + suffix))
    annihilators.append(jw(prefix + [A] + suffix))
    positive_gamma.append(jw(prefix + [X] + suffix))
    negative_gamma.append(jw(prefix + [C] + suffix))

gamma = positive_gamma + negative_gamma
gamma_square = [1] * 5 + [-1] * 5
assert all(gamma[i] * gamma[j] + gamma[j] * gamma[i] == 0
           for i in range(10) for j in range(i))
assert all(gamma[i] * gamma[i] == gamma_square[i] * Id
           for i in range(10))


def flat(M):
    return vector(Q, [M[r, c] for r in range(32) for c in range(32)])


def coordinate_solver(basis):
    columns = matrix(Q, 1024, len(basis),
                     lambda r, j: flat(basis[j])[r])
    rows = list(columns.transpose().pivots())
    square = matrix(Q, len(basis), len(basis),
                    lambda r, c: columns[rows[r], c])

    def coordinates(M):
        rhs = vector(Q, [flat(M)[row] for row in rows])
        result = square.solve_right(rhs)
        assert columns * result == flat(M)
        return result

    return coordinates


witt_basis = []
for i in range(5):
    for j in range(i + 1, 5):
        witt_basis.append(creators[i] * creators[j])
witt_basis += creators[:]
for i in range(5):
    for j in range(5):
        witt_basis.append(creators[i] * annihilators[j] -
                          (1 / 2 if i == j else 0) * Id)
witt_basis += annihilators[:]
for i in range(5):
    for j in range(i + 1, 5):
        witt_basis.append(annihilators[i] * annihilators[j])
witt_coordinates = coordinate_solver(witt_basis)
assert len(witt_basis) == 55

quadratic_coordinates = coordinate_solver(gamma)
split_metric = diagonal_matrix(Q, [1] * 5 + [-1] * 5)


def ordinary_ad(reflector, vector, square):
    return reflector * vector * (reflector / square)


def twisted_ad(reflector, vector, square):
    return -ordinary_ad(reflector, vector, square)


def action_matrix(reflector, square):
    return matrix(Q, 10, 10,
                  lambda r, c: quadratic_coordinates(
                      twisted_ad(reflector, gamma[c], square))[r])


candidate_reports = []
for index, (reflector, square) in enumerate(zip(gamma, gamma_square)):
    orthogonal_action = action_matrix(reflector, square)
    spinor_normalizer = all(
        witt_coordinates(ordinary_ad(reflector, basis, square)) is not None
        for basis in witt_basis)
    candidate_reports.append({
        "label": "gamma%d" % index,
        "raw_square": square,
        "twisted_adjoint_action": {
            "orthogonal": orthogonal_action.transpose() * split_metric *
                orthogonal_action == split_metric,
            "determinant": int(orthogonal_action.det()),
            "square_is_identity": orthogonal_action * orthogonal_action ==
                identity_matrix(Q, 10),
        },
        "spinor_adjoint_normalizes_witt_lie_closure": spinor_normalizer,
    })

mirror = positive_gamma[0] * positive_gamma[1] * positive_gamma[2] * \
    positive_gamma[3] * positive_gamma[4]
mirror_square = 1 if mirror * mirror == Id else -1
mirror_exchange = all(
    ordinary_ad(mirror, creators[i], mirror_square) == annihilators[i]
    for i in range(5))

report = {
    "coefficient_field": "QQ",
    "carrier_dimension": 32,
    "quadratic_dimension": 10,
    "clifford_signature": [5, 5],
    "clifford_generator_count": 10,
    "witt_lie_dimension": 55,
    "candidate_count": len(candidate_reports),
    "candidates": candidate_reports,
    "global_sheet_reflection": {
        "raw_square": mirror_square,
        "exchanges_creation_annihilation": mirror_exchange,
    },
    "pin_cover_target": "Pin(5,5) -> O(5,5)",
    "scope": "explicit_reflection_subsystem_only",
    "weyl_group_identified": False,
}

with open("tools/experiments/cl55_five_grade/export/reflection_candidates.json", "w") as stream:
    json.dump(report, stream, indent=2, sort_keys=True, default=int)

print("SAGE:pin_signature=(5,5)")
print("SAGE:reflection_candidate_count=%d" % len(candidate_reports))
print("SAGE:all_orthogonal=%s" % all(
    item["twisted_adjoint_action"]["orthogonal"]
    for item in candidate_reports))
print("SAGE:all_spinor_normalizers=%s" % all(
    item["spinor_adjoint_normalizes_witt_lie_closure"]
    for item in candidate_reports))
print("SAGE:global_sheet_exchange=%s" % mirror_exchange)
print("SAGE:reflection_report=tools/experiments/cl55_five_grade/export/reflection_candidates.json")
