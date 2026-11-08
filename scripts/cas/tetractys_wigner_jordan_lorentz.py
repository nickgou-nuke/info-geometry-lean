#!/usr/bin/env python3
"""Exact CAS audit of the repository's proposed two-bit Tetractys gammas.

Carrier alignment: InfoGeometry.Clifford.Cl11TensorTower.MatStage 2 is the
four-dimensional real matrix representation built as two Kronecker factors
Matrix (Fin 2) (Fin 2) ℝ.  This audit uses the exact 2x2 real reflection
matrices S=diag(1,-1), Phi=[[0,1],[1,0]], and J=S*Phi from the endogenous
Tetractys convention documented in
InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge.  Kronecker factors
are ordered bit 1 then bit 2 (row-major basis (00,01,10,11)).

The script checks the four gamma squares and anticommutators, Lorentz bivector
commutator action on the span of the four gammas, and the independence of that
span. It also computes the exact coordinates of those gammas in the ordered
Jordan--Wigner monomial basis. These are a CAS-checked coordinate identities;
they are not yet a Lean-proved transport theorem. Exact SymPy arithmetic only.
Run with `python3 scripts/cas/tetractys_wigner_jordan_lorentz.py`.
"""
import json
import hashlib
from pathlib import Path

import sympy as sp

S = sp.Matrix([[1, 0], [0, -1]])
Phi = sp.Matrix([[0, 1], [1, 0]])
I2 = sp.eye(2)
J = S * Phi
eta = [-1, 1, 1, 1]
Eminus = sp.Matrix([[0, 1], [-1, 0]])
pauliX = sp.Matrix([[0, 1], [1, 0]])

def kron(a, b):
    return sp.kronecker_product(a, b)

gammas = [kron(J, I2), kron(S, I2), kron(Phi, S), kron(Phi, Phi)]

# Full two-bit DeWitt tetractys table in bit-1/bit-2 Kronecker order.
bits = [
    {"S": kron(S, I2), "Phi": kron(Phi, I2), "J": kron(J, I2)},
    {"S": kron(I2, S), "Phi": kron(I2, Phi), "J": kron(I2, J)},
]
tetractys_table_checks = 0
for bit in bits:
    for name in ("S", "Phi", "J"):
        op = bit[name]
        expected_sq = -sp.eye(4) if name == "J" else sp.eye(4)
        assert op * op == expected_sq, (name, op * op)
        assert op.T == (-op if name == "J" else op), (name, op.T)
        tetractys_table_checks += 2
    assert bit["S"] * bit["Phi"] == bit["J"]
    assert bit["Phi"] * bit["S"] == -bit["J"]
    assert bit["S"] * bit["J"] == bit["Phi"]
    assert bit["J"] * bit["S"] == -bit["Phi"]
    assert bit["J"] * bit["Phi"] == bit["S"]
    assert bit["Phi"] * bit["J"] == -bit["S"]
    tetractys_table_checks += 6
for left in bits[0].values():
    for right in bits[1].values():
        assert left * right == right * left
        tetractys_table_checks += 1

# Peirce rays are nilpotent and their ordered products recover the diagonal
# idempotents of each bit.
for bit in bits:
    n_plus = (bit["Phi"] + bit["J"]) / 2
    n_minus = (bit["Phi"] - bit["J"]) / 2
    p = (sp.eye(4) + bit["S"]) / 2
    q = (sp.eye(4) - bit["S"]) / 2
    assert n_plus * n_plus == sp.zeros(4)
    assert n_minus * n_minus == sp.zeros(4)
    assert n_plus * n_minus == p
    assert n_minus * n_plus == q
    assert n_plus + n_minus == bit["Phi"]
    assert n_plus - n_minus == bit["J"]
    tetractys_table_checks += 6

anticommutators = {}
for mu in range(4):
    for nu in range(mu, 4):
        value = sp.simplify(gammas[mu] * gammas[nu] + gammas[nu] * gammas[mu])
        expected = 2 * eta[mu] * sp.eye(4) if mu == nu else sp.zeros(4)
        assert value == expected, (mu, nu, value, expected)
        anticommutators[f"{mu},{nu}"] = str(value)

# Bivector action convention is [M_mu_nu, gamma_rho].
action = {}
for mu in range(4):
    for nu in range(mu + 1, 4):
        B = gammas[mu] * gammas[nu]
        for rho in range(4):
            value = sp.simplify(B * gammas[rho] - gammas[rho] * B)
            expected = 2 * ((eta[nu] if rho == nu else 0) * gammas[mu]
                            - (eta[mu] if rho == mu else 0) * gammas[nu])
            assert value == expected, (mu, nu, rho, value, expected)
            action[f"{mu}{nu}:{rho}"] = str(value)

# Flattening the 4 matrices as columns gives rank 4: coefficient coordinates
# in the finite real matrix carrier are unique.
columns = [sp.Matrix(16, 1, list(g)) for g in gammas]
rank = sp.Matrix.hstack(*columns).rank()
assert rank == 4

# Exact two-site Wigner--Jordan tower data, matching
# Cl11TensorTower.wittCreationBase/wittAnnihilationBase and
# jwStringWithBase: the second atom is prefixed by gamma_chiral_base
# = gamma_0_base * gamma_1_base = pauliX * Eminus.
chirality = pauliX * Eminus
jw = [
    kron(pauliX, I2),                 # site 0, Majorana plus
    kron(Eminus, I2),                 # site 0, Majorana minus
    kron(chirality, pauliX),          # site 1, Majorana plus
    kron(chirality, Eminus),          # site 1, Majorana minus
]
jw_eta = [1, -1, 1, -1]
jw_relations = {}
for a in range(4):
    for b in range(a, 4):
        value = sp.simplify(jw[a] * jw[b] + jw[b] * jw[a])
        expected = 2 * jw_eta[a] * sp.eye(4) if a == b else sp.zeros(4)
        assert value == expected, (a, b, value, expected)
        jw_relations[f"{a},{b}"] = str(value)

# Verify the Wigner--Jordan monomials form a basis of Mat_4(R), then compute
# the exact coordinates of every endogenous Tetractys gamma in that basis.
jw_monomials = []
for mask in range(16):
    word = sp.eye(4)
    for i in range(4):
        if mask & (1 << i):
            word = word * jw[i]
    jw_monomials.append(word)
jw_basis_mat = sp.Matrix.hstack(*[
    sp.Matrix(16, 1, list(word)) for word in jw_monomials
])
jw_basis_rank = jw_basis_mat.rank()
assert jw_basis_rank == 16
jw_coordinate_map = {}
for mu, gamma in enumerate(gammas):
    coords = jw_basis_mat.inv() * sp.Matrix(16, 1, list(gamma))
    assert jw_basis_mat * coords == sp.Matrix(16, 1, list(gamma))
    jw_coordinate_map[str(mu)] = [str(sp.factor(x)) for x in coords]

# The full 16-element tensor basis and its coordinates in the two-site
# Wigner--Jordan monomial basis.  Transpose parity gives the 10+6 split.
single_bit_basis = [sp.eye(2), S, Phi, J]
full_tetractys_basis = [kron(a, b)
                        for a in single_bit_basis for b in single_bit_basis]
assert len(full_tetractys_basis) == 16
tetractys_coordinates = {}
for idx, op in enumerate(full_tetractys_basis):
    coords = jw_basis_mat.inv() * sp.Matrix(16, 1, list(op))
    assert jw_basis_mat * coords == sp.Matrix(16, 1, list(op))
    tetractys_coordinates[str(idx)] = [str(sp.factor(x)) for x in coords]
symmetric_count = sum(op.T == op for op in full_tetractys_basis)
skew_count = sum(op.T == -op for op in full_tetractys_basis)
assert (symmetric_count, skew_count) == (10, 6)

# For Omega = J⊗I, each symmetric tensor-basis element S gives ΩS in sp(4,R).
omega = kron(J, I2)
symplectic_generator_checks = 0
for symmetric in full_tetractys_basis:
    if symmetric.T == symmetric:
        X = omega * symmetric
        assert omega * X + X.T * omega == sp.zeros(4)
        symplectic_generator_checks += 1
assert symplectic_generator_checks == 10

# Check closure of the six bivector generators under commutator as a span
# identity: [M_ab,M_cd] has the standard so(3,1) structure constants.
bivectors = {(a, b): gammas[a] * gammas[b]
             for a in range(4) for b in range(a + 1, 4)}
flat_basis = [sp.Matrix(16, 1, list(bivectors[k])) for k in bivectors]
basis_mat = sp.Matrix.hstack(*flat_basis)
closure = {}
for (a, b), X in bivectors.items():
    for (c, d), Y in bivectors.items():
        C = sp.Matrix(16, 1, list(X * Y - Y * X))
        solution = sp.linsolve((basis_mat, C))
        coeffs = next(iter(solution))
        assert all(not x.free_symbols for x in coeffs)
        assert basis_mat * sp.Matrix(coeffs) == C
        closure[f"{a}{b}:{c}{d}"] = [int(x) for x in coeffs]

script = Path(__file__)
artifact = {
    "object": "two_bit_dewitt_tetractys_lorentz_action",
    "lean_owner": "InfoGeometry.Canonical.TetractysRealCliffordTwistorBridge",
    "carrier": "MatStage 2 = Matrix (Fin 4) (Fin 4) ℝ, Kronecker basis (00,01,10,11)",
    "basis_order": ["I", "S", "Phi", "J=S*Phi"],
    "gamma_order": ["J⊗I", "S⊗I", "Phi⊗S", "Phi⊗Phi"],
    "multiplication_convention": "ordinary matrix multiplication; [A,B]=AB-BA",
    "anti_hom": False,
    "checks": {
        "wigner_jordan_cl22_relations": jw_relations,
        "wigner_jordan_monomial_basis_rank": jw_basis_rank,
        "single_bit_tetractys_table_relation_count": tetractys_table_checks,
        "tetractys_gamma_coordinates_in_wigner_jordan_monomials": jw_coordinate_map,
        "two_bit_tetractys_coordinates_in_wigner_jordan_monomials": tetractys_coordinates,
        "two_bit_tetractys_transpose_split": {
            "symmetric": symmetric_count,
            "skew": skew_count,
        },
        "symplectic_generator_checks": symplectic_generator_checks,
        "clifford_relations": anticommutators,
        "lorentz_bivector_vector_action": action,
        "lorentz_bivector_commutator_closure": closure,
        "gamma_span_rank": rank,
    },
    "checked": True,
    "round_trip_verified": False,
    "round_trip_element": "pending Lean kernel transport of the matrix coordinates",
    "scope_limit": "Finite exact Mat_4(R) check only; Lean still needs the monomial-coordinate and representation bridge theorem.",
    "sympy_source": str(script),
    "artifact_hash": hashlib.sha256(script.read_bytes()).hexdigest(),
}
out = script.with_suffix(".json")
out.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
print(json.dumps({"artifact": str(out), "gamma_span_rank": rank,
                  "clifford_relations_checked": len(anticommutators),
                  "wigner_jordan_relations_checked": len(jw_relations),
                  "tetractys_table_relations_checked": tetractys_table_checks,
                  "wigner_jordan_monomial_basis_rank": jw_basis_rank,
                  "two_bit_tetractys_basis_coordinates_checked": len(tetractys_coordinates),
                  "symmetric_skew_split": [symmetric_count, skew_count],
                  "symplectic_generators_checked": symplectic_generator_checks,
                  "tetractys_gammas_translated_to_wigner_jordan_basis": len(jw_coordinate_map),
                  "lorentz_vector_actions_checked": len(action),
                  "lorentz_commutators_checked": len(closure),
                  "source_sha256": artifact["artifact_hash"]}, indent=2))
