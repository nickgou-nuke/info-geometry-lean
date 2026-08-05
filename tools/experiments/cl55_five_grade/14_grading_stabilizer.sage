"""Grading and parabolic action readout for the Cl(5,5) normalizer.

This separates the subgroup stabilizing the centered grading operator N from
the global particle-hole reflection, which reverses all five grades.
"""

load("tools/experiments/cl55_five_grade/01_cl55_witt_generators.sage")
import json


def flat(M):
    return vector(Q, [M[r, c] for r in range(32) for c in range(32)])


def in_span(M, generators):
    return matrix(Q, [flat(X) for X in generators] + [flat(M)]).rank() == len(generators)


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


N_plus = sum((creators[i] * annihilators[i] for i in range(5)),
             zero_matrix(Q, 32))
N_minus = sum((annihilators[i] * creators[i] for i in range(5)),
              zero_matrix(Q, 32))
assert N == (N_plus - N_minus) / 2
assert N_plus + N_minus == 5 * Id

grade_spaces = {
    grade: [X for X, X_grade in zip(lie_basis, lie_grades)
            if X_grade == grade]
    for grade in [-2, -1, 0, 1, 2]
}
positive_parabolic = grade_spaces[0] + grade_spaces[1] + grade_spaces[2]
negative_parabolic = grade_spaces[-2] + grade_spaces[-1] + grade_spaces[0]


def action_report(label, U, target_grade_sign):
    transformed = lambda X: U * X * U.transpose()
    grade_routing = all(
        in_span(transformed(X), grade_spaces[target_grade_sign * grade])
        for grade in grade_spaces
        for X in grade_spaces[grade])
    positive_target = positive_parabolic if target_grade_sign == 1 else negative_parabolic
    negative_target = negative_parabolic if target_grade_sign == 1 else positive_parabolic
    parabolic_routing = (
        all(in_span(transformed(X), positive_target)
            for X in positive_parabolic) and
        all(in_span(transformed(X), negative_target)
            for X in negative_parabolic))
    return {
        "label": label,
        "grade_action": "k_to_%sk" % ("" if target_grade_sign == 1 else "-"),
        "preserves_N": U * N * U.transpose() == N,
        "reverses_N": U * N * U.transpose() == -N,
        "swaps_N_plus_minus": (
            U * N_plus * U.transpose() == N_minus and
            U * N_minus * U.transpose() == N_plus),
        "maps_grade_spaces": grade_routing,
        "preserves_parabolics": parabolic_routing and target_grade_sign == 1,
        "swaps_opposite_parabolics": parabolic_routing and target_grade_sign == -1,
    }


reports = []
for i in range(4):
    permutation = list(range(5))
    permutation[i], permutation[i + 1] = permutation[i + 1], permutation[i]
    reports.append(action_report(
        "mode_swap_%d_%d" % (i, i + 1), permutation_lift(permutation), 1))

local_sign = positive_gamma[0] * negative_gamma[0]
reports.append(action_report("local_particle_hole_candidate", local_sign, 1))

global_sheet = ordered_product(positive_gamma)
reports.append(action_report("global_witt_sheet", global_sheet, -1))

assert all(report["maps_grade_spaces"] for report in reports)
assert all(report["preserves_parabolics"] for report in reports[:5])
assert reports[-1]["swaps_opposite_parabolics"]
assert all(reports[i]["preserves_N"] for i in range(5))
assert reports[-1]["reverses_N"]
assert reports[-1]["swaps_N_plus_minus"]

report = {
    "coefficient_field": "QQ",
    "carrier_dimension": 32,
    "witt_lie_dimension": 55,
    "grade_dimensions": {"-2": 10, "-1": 5, "0": 25, "1": 5, "2": 10},
    "positive_parabolic_grades": [0, 1, 2],
    "negative_parabolic_grades": [-2, -1, 0],
    "grading_stabilizer_generators": 5,
    "global_sheet_reflection_checked": True,
    "all_grade_and_parabolic_routes_verified": True,
    "reports": reports,
}

export_path = (
    "tools/experiments/cl55_five_grade/export/"
    "grading_stabilizer.json")
with open(export_path, "w") as stream:
    json.dump(report, stream, indent=2, sort_keys=True, default=int)

print("SAGE:grading_stabilizer_generators=5")
print("SAGE:grade_and_parabolic_routes_verified=true")
print("SAGE:global_sheet_swaps_N_plus_minus=true")
print("SAGE:global_sheet_reverses_N=true")
print("SAGE:grading_report=%s" % export_path)
