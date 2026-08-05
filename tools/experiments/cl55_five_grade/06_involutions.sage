"""Exact real-linear involution candidates on the Cl(5,5) spinor carrier."""

load("01_cl55_witt_generators.sage")
import json

def flat_matrix(m):
    return vector(Q, [m[r, c] for r in range(32) for c in range(32)])

def preserves_retained(matrix):
    return all(flat.rank() == flat.augment(flat_matrix(matrix * element)).rank()
               for element in basis)

J = identity_matrix(Q, 32)
for g in positive_gamma:
    J = J * g

parity = diagonal_matrix(Q, [(-1) ** bin(x).count("1") for x in range(32)])
mirror_checks = {
    "J_squared": J * J == Id,
    "J_reverses_N": J * N * J == -N,
    "J_creation_to_annihilation": all(J * creators[i] * J == annihilators[i]
                                       for i in range(5)),
    "parity_squared": parity * parity == Id,
    "parity_commutes_N": parity * N == N * parity
}

theta_identity = lambda x: -x.transpose()
theta_identity_preserves = all(
    flat.rank() == flat.augment(flat_matrix(theta_identity(element))).rank()
    for element in basis)

with open("../../../artifacts/cl55_five_grade/involutions.json", "w") as stream:
    json.dump({
        "coefficient_field": "QQ",
        "mirror": mirror_checks,
        "cartan_candidate_minus_transpose_preserves_retained_space":
            theta_identity_preserves,
        "cartan_candidate_status":
            "candidate_only; preservation must be proved or replaced"
    }, stream, indent=2, sort_keys=True)

print("SAGE:involution_report=artifacts/cl55_five_grade/involutions.json")
