"""Independent SageMath check of the real Cl(5,5) Witt five-grade packet.

All coefficients are in QQ. The matrices act on the 32 bitset basis of
Lambda^.(Q^5). This file is an experiment, not a Lean theorem.
"""

import json
import os

Q = QQ
I2 = identity_matrix(Q, 2)
X = matrix(Q, [[0, 1], [1, 0]])
Z = matrix(Q, [[1, 0], [0, -1]])
C = matrix(Q, [[0, 1], [-1, 0]])
R = (X + C) / 2
A = (X - C) / 2

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
    positive_gamma.append(jw(prefix + [X] + suffix))
    negative_gamma.append(jw(prefix + [C] + suffix))
    creators.append(jw(prefix + [R] + suffix))
    annihilators.append(jw(prefix + [A] + suffix))

Id = identity_matrix(Q, 32)
N = sum((creators[i] * annihilators[i] for i in range(5)), zero_matrix(Q, 32)) - (5 / 2) * Id

assert all(g * g == Id for g in positive_gamma)
assert all(g * g == -Id for g in negative_gamma)
all_gamma = positive_gamma + negative_gamma
assert all(all_gamma[i] * all_gamma[j] + all_gamma[j] * all_gamma[i] == 0
           for i in range(10) for j in range(10) if i != j)
assert all(creators[i] * annihilators[j] + annihilators[j] * creators[i] ==
           (Id if i == j else zero_matrix(Q, 32))
           for i in range(5) for j in range(5))

basis = []
grades = []
labels = []
for i in range(5):
    for j in range(i + 1, 5):
        labels.append("c%d%d" % (i, j)); basis.append(creators[i] * creators[j]); grades.append(2)
for i in range(5):
    labels.append("c%d" % i); basis.append(creators[i]); grades.append(1)
for i in range(5):
    for j in range(5):
        labels.append("E%d%d" % (i, j)); basis.append(creators[i] * annihilators[j] - (1/2 if i == j else 0) * Id); grades.append(0)
for i in range(5):
    labels.append("a%d" % i); basis.append(annihilators[i]); grades.append(-1)
for i in range(5):
    for j in range(i + 1, 5):
        labels.append("a%d%d" % (i, j)); basis.append(annihilators[i] * annihilators[j]); grades.append(-2)

flat = matrix(Q, 1024, len(basis),
              lambda r, j: basis[j][r // 32, r % 32])
assert flat.rank() == 55


def flat_vector(M):
    return vector(Q, [M[r, c] for r in range(32) for c in range(32)])


def span_rank(matrices):
    if not matrices:
        return 0
    return matrix(Q, [flat_vector(M) for M in matrices]).rank()


def ordered_product(factors):
    result = Id
    for factor in factors:
        result = result * factor
    return result


# The full associative word envelope is recorded separately.  The words
# c_I a_J form an exact basis of End_Q(Lambda^. Q^5), with integer grade
# |I|-|J|.  This is not the Lie-generated packet below.
associative_words = []
associative_word_grades = []
for creation_mask in range(1 << 5):
    creation_indices = [i for i in range(5) if creation_mask & (1 << i)]
    creation_word = ordered_product([creators[i] for i in creation_indices])
    for annihilation_mask in range(1 << 5):
        annihilation_indices = [i for i in range(4, -1, -1)
                                if annihilation_mask & (1 << i)]
        annihilation_word = ordered_product(
            [annihilators[i] for i in annihilation_indices])
        associative_words.append(creation_word * annihilation_word)
        associative_word_grades.append(
            len(creation_indices) - len(annihilation_indices))

assert span_rank(associative_words) == 1024
associative_grade_dimensions = {
    grade: span_rank([word for word, word_grade in
                      zip(associative_words, associative_word_grades)
                      if word_grade == grade])
    for grade in range(-5, 6)
}
assert sum(associative_grade_dimensions.values()) == 1024
assert associative_grade_dimensions[3] != 0


def add_independent(generators, generator_grades, generator_labels,
                    candidate, candidate_grade, candidate_label):
    if candidate == zero_matrix(Q, 32):
        return False
    if span_rank(generators + [candidate]) == len(generators):
        return False
    generators.append(candidate)
    generator_grades.append(candidate_grade)
    generator_labels.append(candidate_label)
    return True


# Lie closure from Witt generators only. Products are never inserted as
# generators except when they arise as an ordinary commutator.
lie_basis = creators[:] + annihilators[:]
lie_grades = [1] * 5 + [-1] * 5
lie_labels = ["c%d" % i for i in range(5)] + ["a%d" % i for i in range(5)]
changed = True
while changed:
    changed = False
    old_basis = lie_basis[:]
    old_grades = lie_grades[:]
    old_labels = lie_labels[:]
    for i in range(len(old_basis)):
        for j in range(i + 1, len(old_basis)):
            bracket = old_basis[i] * old_basis[j] - old_basis[j] * old_basis[i]
            if add_independent(
                    lie_basis, lie_grades, lie_labels, bracket,
                    old_grades[i] + old_grades[j],
                    "[%s,%s]" % (old_labels[i], old_labels[j])):
                changed = True

lie_grade_dimensions = {
    grade: span_rank([X for X, X_grade in zip(lie_basis, lie_grades)
                      if X_grade == grade])
    for grade in range(-5, 6)
}
assert len(lie_basis) == 55
assert lie_grade_dimensions == {
    -5: 0, -4: 0, -3: 0, -2: 10, -1: 5,
    0: 25, 1: 5, 2: 10, 3: 0, 4: 0, 5: 0,
}

obstruction_pairs = {}
for left_grade, right_grade in [(2, 1), (-2, -1), (2, 2), (-2, -2)]:
    left = [X for X, X_grade in zip(lie_basis, lie_grades)
            if X_grade == left_grade]
    right = [X for X, X_grade in zip(lie_basis, lie_grades)
             if X_grade == right_grade]
    obstruction_pairs["%+d,%+d" % (left_grade, right_grade)] = any(
        X * Y - Y * X != zero_matrix(Q, 32) for X in left for Y in right)

# The full matrix commutator algebra is the traceless subspace. Verify its
# standard matrix-unit basis has the expected exact dimension.
matrix_units = []
for i in range(32):
    for j in range(32):
        Eij = zero_matrix(Q, 32)
        Eij[i, j] = 1
        matrix_units.append(Eij)
sl_basis = [matrix_units[i * 32 + j]
            for i in range(32) for j in range(32) if i != j]
sl_basis += [matrix_units[i * 32 + i] - matrix_units[0]
             for i in range(1, 32)]
assert span_rank(sl_basis) == 1023

nonzero = 0
routing = True
for i in range(len(basis)):
    for j in range(len(basis)):
        bracket = basis[i] * basis[j] - basis[j] * basis[i]
        if bracket != zero_matrix(Q, 32):
            nonzero += 1
            expected = grades[i] + grades[j]
            if N * bracket - bracket * N != expected * bracket:
                routing = False

J = identity_matrix(Q, 32)
for g in positive_gamma:
    J = J * g
assert J * J == Id
assert J * N * J == -N
assert all(J * creators[i] * J == annihilators[i] for i in range(5))

print("SAGE:field=QQ")
print("SAGE:spinor_dimension=32")
print("SAGE:cl55_relations=true")
print("SAGE:basis_rank=%d" % flat.rank())
print("SAGE:grade_dimensions=-2:10,-1:5,0:25,1:5,2:10")
print("SAGE:nonzero_brackets=%d" % nonzero)
print("SAGE:routing_verified=%s" % routing)
print("SAGE:mirror_squared=true")
print("SAGE:mirror_reverses_N=true")
print("SAGE:associative_word_envelope_dimension=1024")
print("SAGE:associative_grade_support=-5..5")
print("SAGE:associative_nonzero_grade_plus_3=true")
print("SAGE:full_envelope_commutator_dimension=1023")
print("SAGE:lie_from_witt_generators_dimension=%d" % len(lie_basis))
print("SAGE:lie_from_witt_grade_dimensions=-2:10,-1:5,0:25,1:5,2:10")
print("SAGE:lie_obstructions=%s" % obstruction_pairs)

export_dir = os.path.join(
    os.getcwd(), "tools", "experiments", "cl55_five_grade", "export")
if not os.path.isdir(export_dir):
    os.makedirs(export_dir)

associative_grade_dimensions_json = {
    int(grade): int(dimension)
    for grade, dimension in associative_grade_dimensions.items()
}
lie_grade_dimensions_json = {
    int(grade): int(dimension)
    for grade, dimension in lie_grade_dimensions.items()
}

report = {
    "coefficient_field": "QQ",
    "spinor_dimension": 32,
    "associative_generator_closure": {
        "dimension": 1024,
        "algebra": "M_32(QQ)",
        "grade_min": -5,
        "grade_max": 5,
        "grade_dimensions": associative_grade_dimensions_json,
        "nonzero_grade_plus_3": True,
    },
    "full_envelope_commutator_algebra": {
        "dimension": 1023,
        "candidate": "sl_32(QQ)",
    },
    "witt_generator_lie_closure": {
        "generators": "c_i,a_i",
        "bracket": "ordinary_commutator",
        "dimension": len(lie_basis),
        "grade_dimensions": lie_grade_dimensions_json,
        "obstruction_pairs_nonzero": obstruction_pairs,
    },
}
with open(os.path.join(export_dir, "closure_report.json"), "w") as report_file:
    json.dump(report, report_file, indent=2, sort_keys=True, default=int)

with open(os.path.join(export_dir, "grades.json"), "w") as grades_file:
    json.dump({
        "associative": associative_grade_dimensions_json,
        "witt_lie": lie_grade_dimensions_json,
    }, grades_file, indent=2, sort_keys=True, default=int)
