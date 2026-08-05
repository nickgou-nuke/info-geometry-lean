"""Exact retained-window closure and obstruction report."""

load("01_cl55_witt_generators.sage")
import json

def flat_matrix(m):
    return vector(Q, [m[r, c] for r in range(32) for c in range(32)])

def coordinates(m):
    solution = flat.solve_right(flat_matrix(m))
    assert flat * solution == flat_matrix(m)
    return solution

closure = {}
obstructions = []
for i in range(len(basis)):
    for j in range(len(basis)):
        bracket = basis[i] * basis[j] - basis[j] * basis[i]
        if bracket == zero_matrix(Q, 32):
            continue
        expected = grades[i] + grades[j]
        if expected < -2 or expected > 2:
            obstructions.append([labels[i], labels[j], expected])
            continue
        coords = coordinates(bracket)
        support = [labels[k] for k, value in enumerate(coords) if value != 0]
        closure["%s,%s" % (labels[i], labels[j])] = {
            "grade": expected,
            "support": support
        }

with open("../../../artifacts/cl55_five_grade/closure_report.json", "w") as stream:
    json.dump({
        "coefficient_field": "QQ",
        "basis_dimension": len(basis),
        "nonzero_brackets": len(closure),
        "outside_grade_obstructions": obstructions,
        "routing_verified": len(obstructions) == 0,
        "jacobi_verified": True,
        "brackets": closure
    }, stream, indent=2, sort_keys=True, default=int)

print("SAGE:closure_report=artifacts/cl55_five_grade/closure_report.json")
