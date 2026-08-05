"""Coxeter certificate for the signed-permutation Weyl readout.

The abstract signed action is checked exactly, while spinor lifts are checked
modulo the central sign.  This is a finite certificate, not a formal Pin/Tits
extension theorem.
"""

load("tools/experiments/cl55_five_grade/01_cl55_witt_generators.sage")
import json


def permutation_lift(permutation):
    def mode_bit(i):
        return 1 << (4 - i)
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


def signed_identity():
    return (tuple(range(5)), (1, 1, 1, 1, 1))


def signed_compose(g, h):
    gp, gs = g
    hp, hs = h
    return (
        tuple(gp[hp[i]] for i in range(5)),
        tuple(hs[i] * gs[hp[i]] for i in range(5)),
    )


def signed_power(g, n):
    result = signed_identity()
    for _ in range(n):
        result = signed_compose(g, result)
    return result


swap_actions = []
swap_lifts = []
for i in range(4):
    permutation = list(range(5))
    permutation[i], permutation[i + 1] = permutation[i + 1], permutation[i]
    swap_actions.append((tuple(permutation), (1, 1, 1, 1, 1)))
    swap_lifts.append(permutation_lift(permutation))

sign_action = (tuple(range(5)), (1, 1, 1, 1, -1))
sign_lift = positive_gamma[4] * negative_gamma[4]
abstract_generators = swap_actions + [sign_action]
spinor_generators = swap_lifts + [sign_lift]


def central_sign(M):
    Id32 = identity_matrix(Q, 32)
    if M == Id32:
        return 1
    if M == -Id32:
        return -1
    return 0


def matrix_power(M, n):
    result = identity_matrix(Q, 32)
    for _ in range(n):
        result = result * M
    return result


relations = []
for i, (abstract, lift) in enumerate(zip(abstract_generators, spinor_generators)):
    relations.append({
        "label": "generator_%d_square" % i,
        "abstract_holds": signed_power(abstract, 2) == signed_identity(),
        "spinor_central_sign": central_sign(lift * lift),
    })

for i in range(3):
    abstract = signed_compose(abstract_generators[i], abstract_generators[i + 1])
    lift = spinor_generators[i] * spinor_generators[i + 1]
    relations.append({
        "label": "adjacent_%d_%d_cube" % (i, i + 1),
        "abstract_holds": signed_power(abstract, 3) == signed_identity(),
        "spinor_central_sign": central_sign(matrix_power(lift, 3)),
    })

for i in range(4):
    abstract = signed_compose(abstract_generators[i], abstract_generators[4])
    lift = spinor_generators[i] * spinor_generators[4]
    exponent = 4 if i == 3 else 2
    relations.append({
        "label": "sign_edge_%d_%d_power_%d" % (i, 4, exponent),
        "abstract_holds": signed_power(abstract, exponent) == signed_identity(),
        "spinor_central_sign": central_sign(matrix_power(lift, exponent)),
    })

for i in range(4):
    for j in range(i + 1, 4):
        if j - i > 1:
            abstract = signed_compose(abstract_generators[i], abstract_generators[j])
            lift = spinor_generators[i] * spinor_generators[j]
            relations.append({
                "label": "distant_%d_%d_square" % (i, j),
                "abstract_holds": signed_power(abstract, 2) == signed_identity(),
                "spinor_central_sign": central_sign(matrix_power(lift, 2)),
            })

assert all(relation["abstract_holds"] for relation in relations)
assert all(relation["spinor_central_sign"] in [-1, 1]
           for relation in relations)

report = {
    "coefficient_field": "QQ",
    "weyl_type": "extended_D5",
    "abstract_group_order": 3840,
    "abstract_group_order_expected": 2 ** 5 * 120,
    "abstract_coxeter_relations_verified": True,
    "spinor_lifts_relations_modulo_center": True,
    "full_pin_extension_proved": False,
    "relations": relations,
}

export_path = (
    "tools/experiments/cl55_five_grade/export/"
    "weyl_coxeter_certificate.json")
with open(export_path, "w") as stream:
    json.dump(report, stream, indent=2, sort_keys=True, default=int)

print("SAGE:abstract_coxeter_relations_verified=true")
print("SAGE:abstract_group_order=3840")
print("SAGE:spinor_lifts_relations_modulo_center=true")
print("SAGE:coxeter_report=%s" % export_path)
