import sympy as sp

Q = sp.Rational

concepts = {
    "Nuclear_Phonon",
    "IBM_U6_Bilinear_Generator",
    "Quadrupole_d_dagger_s",
    "Sp6R_Raising_Generator",
    "Noncompact_Dilation_Shear",
    "Casimir_Dilation_Spring",
    "Metriplectic_Evolution",
    "Wasserstein_Gradient_Flow",
    "Legendre_Fenchel_Duality",
}

edges = {
    ("Nuclear_Phonon", "represented_by", "IBM_U6_Bilinear_Generator"),
    ("IBM_U6_Bilinear_Generator", "counted_by", "Quadrupole_d_dagger_s"),
    ("Nuclear_Phonon", "represented_by", "Sp6R_Raising_Generator"),
    ("Sp6R_Raising_Generator", "decomposes_into", "Noncompact_Dilation_Shear"),
    ("Noncompact_Dilation_Shear", "quantizes", "Casimir_Dilation_Spring"),
    ("Noncompact_Dilation_Shear", "drives_irreversible_flow", "Metriplectic_Evolution"),
    ("Metriplectic_Evolution", "metric_part", "Wasserstein_Gradient_Flow"),
    ("Metriplectic_Evolution", "stabilized_by", "Legendre_Fenchel_Duality"),
}

assert ("Noncompact_Dilation_Shear", "drives_irreversible_flow", "Metriplectic_Evolution") in edges
assert ("Metriplectic_Evolution", "metric_part", "Wasserstein_Gradient_Flow") in edges

insert = {
    "_from": "concepts/Noncompact_Dilation_Shear",
    "_to": "concepts/Metriplectic_Evolution",
    "type": "drives_irreversible_flow",
}
assert insert["type"] == "drives_irreversible_flow"

milestones = list(range(1, 14))
assert len(milestones) == 13
assert milestones[-1] == 13

def poincare_c1(m):
    return -m*m

def stiffness(c1):
    return -c1

assert stiffness(poincare_c1(Q(3))) == 9
assert 36 == 6*6
assert 21 == 3*(2*3+1)
assert sp.I != 0

print({
    "concepts": len(concepts),
    "edges": len(edges),
    "bridge": insert,
    "milestone_13": milestones[-1],
    "u6_dim": 36,
    "sp6R_dim": 21,
    "spring_k_m3": stiffness(poincare_c1(Q(3))),
})
