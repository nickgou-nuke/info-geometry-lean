"""Exact finite Weyl-normalizer checks for the Cl(5,5) Witt packet.

This is computational evidence only.  The signed permutations act on the
five mode space and are lifted to the exterior-algebra spinor carrier.  The
script separates the finite Weyl action from the connected 55-dimensional
Lie algebra; it does not identify a full Pin normalizer or a Lie-group
extension theorem.
"""

load("tools/experiments/cl55_five_grade/01_cl55_witt_generators.sage")
import json


def flat_vector(M):
    return vector(Q, [M[r, c] for r in range(32) for c in range(32)])


def span_rank(matrices):
    if not matrices:
        return 0
    return matrix(Q, [flat_vector(M) for M in matrices]).rank()


def in_span(M, generators):
    return span_rank(generators + [M]) == span_rank(generators)


def conjugate(U, X):
    return U * X * U.transpose()


def mode_bit(i):
    # The Jordan-Wigner tensor basis orders the first mode in the high bit.
    return 1 << (4 - i)


def permutation_lift(permutation):
    """Lift a permutation of the five modes to Lambda^.(Q^5)."""
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


def signed_action_identity():
    return (tuple(range(5)), (1, 1, 1, 1, 1))


def signed_action_compose(g, h):
    """Composition g after h for c_i |-> sign_i c_{permutation_i}."""
    gp, gs = g
    hp, hs = h
    return (
        tuple(gp[hp[i]] for i in range(5)),
        tuple(hs[i] * gs[hp[i]] for i in range(5)),
    )


def signed_action_generators():
    result = []
    for i in range(4):
        permutation = list(range(5))
        permutation[i], permutation[i + 1] = permutation[i + 1], permutation[i]
        result.append((tuple(permutation), (1, 1, 1, 1, 1)))
    signs = [1, 1, 1, 1, 1]
    signs[0] = -1
    result.append((tuple(range(5)), tuple(signs)))
    return result


witt_basis = lie_basis
assert span_rank(witt_basis) == 55
cartan = [
    creators[i] * annihilators[i] - (1 / 2) * Id
    for i in range(5)
]

mode_permutations = []
for i in range(4):
    permutation = list(range(5))
    permutation[i], permutation[i + 1] = permutation[i + 1], permutation[i]
    mode_permutations.append(("swap%d%d" % (i, i + 1), tuple(permutation)))

generator_reports = []
for label, permutation in mode_permutations:
    U = permutation_lift(permutation)
    assert U * U.transpose() == Id
    assert U * N * U.transpose() == N
    normalizes = all(in_span(conjugate(U, X), witt_basis) for X in witt_basis)
    cartan_action = all(
        conjugate(U, cartan[i]) == cartan[permutation[i]]
        for i in range(5))
    generator_reports.append({
        "label": label,
        "kind": "mode_permutation_reflection",
        "square_is_identity": True,
        "preserves_grading_operator": True,
        "normalizes_witt_lie_span": normalizes,
        "conjugates_cartan": cartan_action,
    })

sign_lift = positive_gamma[0] * negative_gamma[0]
assert sign_lift * sign_lift == Id
assert sign_lift * N * sign_lift == N
sign_normalizes = all(
    in_span(conjugate(sign_lift, X), witt_basis) for X in witt_basis)
sign_cartan_action = all(
    conjugate(sign_lift, cartan[i]) == cartan[i]
    for i in range(5))
generator_reports.append({
    "label": "sign_mode0",
    "kind": "mode_sign_reflection",
    "square_is_identity": True,
    "preserves_grading_operator": True,
    "normalizes_witt_lie_span": sign_normalizes,
    "conjugates_cartan": sign_cartan_action,
})

assert all(report["square_is_identity"] for report in generator_reports)
assert all(report["preserves_grading_operator"] for report in generator_reports)
assert all(report["normalizes_witt_lie_span"] for report in generator_reports)
assert all(report["conjugates_cartan"] for report in generator_reports)

identity = signed_action_identity()
seen = {identity}
frontier = [identity]
generators = signed_action_generators()
while frontier:
    current = frontier.pop()
    for generator in generators:
        candidate = signed_action_compose(generator, current)
        if candidate not in seen:
            seen.add(candidate)
            frontier.append(candidate)

expected_order = (2 ** 5) * 120
assert len(seen) == expected_order

report = {
    "coefficient_field": "QQ",
    "carrier_dimension": 32,
    "identity_component_lie_dimension": 55,
    "generator_count": len(generator_reports),
    "generator_reports": generator_reports,
    "weyl_type": "B5",
    "weyl_group_order": len(seen),
    "expected_weyl_group_order": expected_order,
    "weyl_group_identified": len(seen) == expected_order,
    "normalizer_scope": "signed_mode_permutations_on_spinor_carrier",
    "pin_group_extension_proved": False,
}

export_dir = "tools/experiments/cl55_five_grade/export"
with open(export_dir + "/weyl_group_normalizer.json", "w") as stream:
    json.dump(report, stream, indent=2, sort_keys=True, default=int)

print("SAGE:weyl_generator_count=%d" % len(generator_reports))
print("SAGE:weyl_group_order=%d" % len(seen))
print("SAGE:weyl_group_expected_order=%d" % expected_order)
print("SAGE:weyl_generators_normalize=true")
print("SAGE:weyl_report=%s/weyl_group_normalizer.json" % export_dir)
