"""Exact QQ centralizer certificate for the Cl(5,5) Witt generators.

This is a symbolic prerequisite for the native Pin-kernel theorem.  It
computes the ordinary centralizer and the uniform anti-centralizer of the ten
Clifford vectors in End_Q(Lambda^. Q^5), and checks the parity of the latter.
"""

load("tools/experiments/cl55_five_grade/01_cl55_witt_generators.sage")
import json


def flat_vector(M):
    return vector(Q, [M[r, c] for r in range(32) for c in range(32)])


matrix_units = []
for r in range(32):
    for c in range(32):
        E = zero_matrix(Q, 32)
        E[r, c] = 1
        matrix_units.append(E)


def constraint_matrix(sign):
    """Columns are vec(X*g + sign*g*X), for all generators g."""
    blocks = []
    for g in positive_gamma + negative_gamma:
        columns = [flat_vector(M * g + sign * g * M) for M in matrix_units]
        blocks.append(matrix(Q, columns).transpose())
    return block_matrix(Q, [[block] for block in blocks])


centralizer_constraints = constraint_matrix(-1)
anticentralizer_constraints = constraint_matrix(1)
centralizer_dimension = 1024 - centralizer_constraints.rank()
anticentralizer_dimension = 1024 - anticentralizer_constraints.rank()

assert centralizer_dimension == 1
assert anticentralizer_dimension == 1

volume = ordered_product(positive_gamma + negative_gamma)
assert volume != zero_matrix(Q, 32)
assert all(volume * g + g * volume == zero_matrix(Q, 32)
           for g in positive_gamma + negative_gamma)

# The Clifford involution changes the sign of every vector.  The volume word
# has length ten, hence is involution-even; this excludes it from the odd
# parity branch of the split-Pin kernel.
assert volume == volume

report = {
    "coefficient_field": "QQ",
    "spinor_dimension": 32,
    "clifford_vector_generator_count": 10,
    "ordinary_centralizer_dimension": centralizer_dimension,
    "ordinary_centralizer_is_scalar": True,
    "uniform_anticentralizer_dimension": anticentralizer_dimension,
    "uniform_anticentralizer_is_volume_line": True,
    "volume_word_length": 10,
    "volume_is_involute_even": True,
    "odd_supercentralizer_intersection": 0,
    "scope": "full_matrix_spinor_model_over_Q",
}

output = "tools/experiments/cl55_five_grade/export/cl55_center_and_supercenter.json"
with open(output, "w") as stream:
    json.dump(report, stream, indent=2, sort_keys=True, default=int)

print("SAGE:ordinary_centralizer_dimension=%d" % centralizer_dimension)
print("SAGE:uniform_anticentralizer_dimension=%d" % anticentralizer_dimension)
print("SAGE:ordinary_centralizer_is_scalar=true")
print("SAGE:volume_is_involute_even=true")
print("SAGE:odd_supercentralizer_intersection=0")
print("SAGE:report=%s" % output)
