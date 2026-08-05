"""Exact Cartan-weight readout for the retained B5 candidate."""

load("01_cl55_witt_generators.sage")
import json

def flat_matrix(m):
    return vector(Q, [m[r, c] for r in range(32) for c in range(32)])

cartan = [creators[i] * annihilators[i] - (1/2) * Id for i in range(5)]
weights = {}
for label, element in zip(labels, basis):
    weight = []
    for h in cartan:
        commutator = h * element - element * h
        if commutator == zero_matrix(Q, 32):
            weight.append(0)
        else:
            scalar = None
            for entry_x, entry_y in zip(flat_matrix(commutator), flat_matrix(element)):
                if entry_y != 0:
                    scalar = entry_x / entry_y
                    break
            if scalar is None or commutator != scalar * element:
                raise ValueError("non-weight vector: %s" % label)
            weight.append(str(scalar))
    weights[label] = weight

with open("../../../artifacts/cl55_five_grade/root_weights.json", "w") as stream:
    json.dump({"coefficient_field": "QQ", "weights": weights},
              stream, indent=2, sort_keys=True, default=int)

print("SAGE:root_weights=artifacts/cl55_five_grade/root_weights.json")
