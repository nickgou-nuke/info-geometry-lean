"""Export rational structure constants for the retained ordinary Lie bracket."""

load("01_cl55_witt_generators.sage")
import json

def flat_matrix(m):
    return vector(Q, [m[r, c] for r in range(32) for c in range(32)])

def coordinates(m):
    solution = flat.solve_right(flat_matrix(m))
    assert flat * solution == flat_matrix(m)
    return solution

constants = []
for i in range(len(basis)):
    for j in range(len(basis)):
        bracket = basis[i] * basis[j] - basis[j] * basis[i]
        coords = coordinates(bracket)
        for k, value in enumerate(coords):
            if value != 0:
                constants.append({"i": i, "j": j, "k": k,
                                  "value": str(value)})

with open("../../../artifacts/cl55_five_grade/structure_constants.json", "w") as stream:
    json.dump({
        "coefficient_field": "QQ",
        "basis_labels": labels,
        "basis_grades": grades,
        "dimension": len(basis),
        "nonzero_structure_constants": constants
    }, stream, indent=2, sort_keys=True, default=int)

print("SAGE:structure_constants=artifacts/cl55_five_grade/structure_constants.json")
