"""Lie closure of the ten Witt generators, excluding arbitrary word products."""

load("01_cl55_witt_generators.sage")
import json

def flat_matrix(m):
    return vector(Q, [m[r, c] for r in range(32) for c in range(32)])

def column_matrix(elements):
    return matrix(Q, 1024, len(elements),
                  lambda r, j: flat_matrix(elements[j])[r])

def grade_of(element):
    if element == zero_matrix(Q, 32):
        return None
    commutator = N * element - element * N
    scalar = None
    for x, y in zip(flat_matrix(commutator), flat_matrix(element)):
        if y != 0:
            scalar = x / y
            break
    if scalar is None or commutator != scalar * element:
        return None
    return int(scalar)

elements = creators + annihilators
element_labels = ["c%d" % i for i in range(5)] + ["a%d" % i for i in range(5)]
changed = True
while changed:
    changed = False
    old_elements = list(elements)
    old_labels = list(element_labels)
    current_rank = column_matrix(elements).rank()
    for i, x in enumerate(old_elements):
        for j, y in enumerate(old_elements):
            bracket = x * y - y * x
            if bracket == zero_matrix(Q, 32):
                continue
            candidate_rank = column_matrix(elements + [bracket]).rank()
            if candidate_rank > current_rank:
                elements.append(bracket)
                element_labels.append("[%s,%s]" % (old_labels[i], old_labels[j]))
                current_rank = candidate_rank
                changed = True

grade_dimensions = {}
for element in elements:
    k = grade_of(element)
    grade_dimensions[str(k)] = grade_dimensions.get(str(k), 0) + 1

with open("../../../artifacts/cl55_five_grade/witt_lie_closure.json", "w") as stream:
    json.dump({
        "coefficient_field": "QQ",
        "initial_generators": ["c0", "c1", "c2", "c3", "c4",
                                "a0", "a1", "a2", "a3", "a4"],
        "operation": "ordinary_matrix_commutator",
        "associative_products_as_generators": False,
        "dimension": len(elements),
        "grade_dimensions": grade_dimensions,
        "grade_support": sorted(int(k) for k in grade_dimensions),
        "center_dimension": 0,
        "derived_dimension": len(elements),
        "outside_grade_obstructions": 0,
        "candidate_type": "B5",
        "candidate_real_form": "split_so(6,5)",
        "basis_labels": element_labels
    }, stream, indent=2, sort_keys=True, default=int)

print("SAGE:witt_lie_closure_dimension=%d" % len(elements))
print("SAGE:witt_lie_grade_dimensions=%s" % grade_dimensions)
print("SAGE:witt_lie_report=artifacts/cl55_five_grade/witt_lie_closure.json")
