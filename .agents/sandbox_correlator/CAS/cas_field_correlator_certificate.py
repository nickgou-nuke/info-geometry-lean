#!/usr/bin/env python3
"""
cas_field_correlator_certificate.py

SymPy Symbolic Certificate Generator for FieldCorrelatorProjection Invariants:
1. FieldCorrelator & DetectorProjector:
   - Single projector linearity: D(r1*F1 + r2*F2) = r1*D(F1) + r2*D(F2)
   - Pair projector bilinear scale: (eps1 * eps2) * (a * b) = (eps1 * a) * (eps2 * b)
   - Kronecker tensor product factorization: (D1 (x) D2)(v1 (x) v2) = (D1 v1) (x) (D2 v2)
2. ModeProjection:
   - Mode trace nullspace annihilation: modeTrace(m, o) = m + 0*o = m
   - Orthogonal projection matrix algebra: Pi_0^2 = Pi_0, Pi_1^2 = Pi_1, Pi_0 * Pi_1 = 0, Pi_0 + Pi_1 = I_2
   - Annihilation functional: T * Pi_1 = [0, 0]
   - Trace linearity: modeTrace(r1*m1 + r2*m2, r1*o1 + r2*o2) = r1*modeTrace(m1, o1) + r2*modeTrace(m2, o2)
3. RankHierarchy:
   - singlesCount degree 1 in X: S(N0, eps, X) = (N0 * eps) * X
   - coincidenceCount degree 2 in X: C(N0, K, X) = (N0 * K) * X^2
   - Coincidence parabola identity: C(N0, K, X) - (N0 * K) * X^2 == 0
   - Scale-invariant coordinate ratio: C(X) / S(X)^2 = K / (N0 * eps^2) (degree 0 in X)
4. CausalPoset:
   - Archetype rank vector: [195, 196, 197, 198, 199]
   - Step deltas: [1, 1, 1, 1] (strictly positive, monotonic)
   - Injectivity: 5 distinct values (kernel contradiction for off-diagonals)
   - Order axioms: Reflexivity, Transitivity, Antisymmetry over all Archetype pairs/triples
   - Canonical chain inequalities: 195 <= 196 <= 197 <= 198 <= 199

Emits certificate.json and outputs verification status.
"""

from __future__ import annotations
import json
import os
import sys
from typing import Any, Dict, List
import sympy as sp

def generate_field_correlator_certificates() -> Dict[str, Any]:
    print("=== Generating FieldCorrelatorProjection CAS Certificates ===")
    
    # -------------------------------------------------------------
    # 1. Field Correlator & Detector Projector
    # -------------------------------------------------------------
    eps1, eps2, singleEff, pairEff = sp.symbols('eps1 eps2 singleEff pairEff', real=True)
    a, b, a1, b1, a2, b2 = sp.symbols('a b a1 b1 a2 b2', real=True)
    r1, r2 = sp.symbols('r1 r2', real=True)

    # Single projector linearity
    # projectSingle(det, <r1*a1 + r2*a2, r1*b1 + r2*b2>) = singleEff * (r1*a1 + r2*a2)
    lhs_single = singleEff * (r1 * a1 + r2 * a2)
    rhs_single = r1 * (singleEff * a1) + r2 * (singleEff * a2)
    diff_single = sp.simplify(lhs_single - rhs_single)
    assert diff_single == 0, f"Single projector linearity failed: {diff_single}"

    # Pair projector bilinear scale
    lhs_pair = (eps1 * eps2) * (a * b)
    rhs_pair = (eps1 * a) * (eps2 * b)
    diff_pair = sp.simplify(lhs_pair - rhs_pair)
    assert diff_pair == 0, f"Pair projector bilinear scale failed: {diff_pair}"

    # Tensor product representation
    D1 = sp.Matrix([[eps1]])
    D2 = sp.Matrix([[eps2]])
    v1 = sp.Matrix([[a]])
    v2 = sp.Matrix([[b]])
    D_kron = sp.kronecker_product(D1, D2)
    v_kron = sp.kronecker_product(v1, v2)
    lhs_kron = D_kron * v_kron
    rhs_kron = sp.kronecker_product(D1 * v1, D2 * v2)
    assert lhs_kron == rhs_kron, "Kronecker tensor product factorization failed"

    # -------------------------------------------------------------
    # 2. Mode Projection & Nullspace Annihilation
    # -------------------------------------------------------------
    monopole, oscillatory = sp.symbols('monopole oscillatory', real=True)
    m1, o1, m2, o2 = sp.symbols('m1 o1 m2 o2', real=True)

    # modeTrace definition: monopole + 0 * oscillatory
    mode_trace_def = monopole + 0 * oscillatory
    assert sp.simplify(mode_trace_def - monopole) == 0

    # Linearity of modeTrace
    lhs_mt_lin = (r1 * m1 + r2 * m2) + 0 * (r1 * o1 + r2 * o2)
    rhs_mt_lin = r1 * (m1 + 0 * o1) + r2 * (m2 + 0 * o2)
    assert sp.simplify(lhs_mt_lin - rhs_mt_lin) == 0

    # Orthogonal projection matrices
    Pi_0 = sp.Matrix([[1, 0], [0, 0]])
    Pi_1 = sp.Matrix([[0, 0], [0, 1]])
    I2 = sp.eye(2)
    T = sp.Matrix([[1, 0]])

    assert Pi_0 * Pi_0 == Pi_0, "Pi_0 is not idempotent"
    assert Pi_1 * Pi_1 == Pi_1, "Pi_1 is not idempotent"
    assert Pi_0 * Pi_1 == sp.zeros(2, 2), "Pi_0 * Pi_1 != 0"
    assert Pi_1 * Pi_0 == sp.zeros(2, 2), "Pi_1 * Pi_0 != 0"
    assert Pi_0 + Pi_1 == I2, "Pi_0 + Pi_1 != I2"
    assert T * Pi_1 == sp.zeros(1, 2), "T * Pi_1 != 0 (mode nullspace annihilation failed)"

    # Action on arbitrary mode vector [m, o]^T
    v_mode = sp.Matrix([[monopole], [oscillatory]])
    v_projected_0 = Pi_0 * v_mode
    v_projected_1 = Pi_1 * v_mode
    assert v_projected_0 == sp.Matrix([[monopole], [0]])
    assert v_projected_1 == sp.Matrix([[0], [oscillatory]])
    assert T * v_projected_0 == sp.Matrix([[monopole]])
    assert T * v_projected_1 == sp.Matrix([[0]])

    # -------------------------------------------------------------
    # 3. Rank Hierarchy & Parabolic Invariant
    # -------------------------------------------------------------
    N0, eps, K, X = sp.symbols('N0 eps K X', real=True)
    singles = N0 * eps * X
    coincidences = N0 * K * X**2

    poly_singles = sp.Poly(singles, X)
    poly_coinc = sp.Poly(coincidences, X)

    assert poly_singles.degree() == 1, f"Singles degree != 1: {poly_singles.degree()}"
    assert poly_coinc.degree() == 2, f"Coincidences degree != 2: {poly_coinc.degree()}"

    # Parabolic coordinate identity
    parabola_diff = sp.simplify(coincidences - (N0 * K) * X**2)
    assert parabola_diff == 0, f"Parabola identity failed: {parabola_diff}"

    # Scale-invariant ratio
    ratio = sp.cancel(coincidences / (singles**2))
    expected_ratio = K / (N0 * eps**2)
    assert sp.simplify(ratio - expected_ratio) == 0, f"Scale-invariant ratio mismatch: {ratio}"
    assert not ratio.has(X), "Ratio unexpectedly depends on coordinate X"

    # -------------------------------------------------------------
    # 4. Causal Poset & Archetype Ranks
    # -------------------------------------------------------------
    archetypes = [
        "fieldCorrelator",
        "detectorProjector",
        "modeNullspace",
        "rankHierarchy",
        "scaleInvariantObservable"
    ]
    ranks = {
        "fieldCorrelator": 195,
        "detectorProjector": 196,
        "modeNullspace": 197,
        "rankHierarchy": 198,
        "scaleInvariantObservable": 199
    }
    rank_list = [ranks[a] for a in archetypes]

    # Monotonicity check
    deltas = [int(rank_list[i+1] - rank_list[i]) for i in range(len(rank_list)-1)]
    assert all(d == 1 for d in deltas), f"Deltas not all 1: {deltas}"

    # Injectivity check
    assert len(set(rank_list)) == len(rank_list), "Ranks are not strictly injective"

    # Poset axioms verification over finite domain
    def precedes(a1_name: str, a2_name: str) -> bool:
        return ranks[a1_name] <= ranks[a2_name]

    # Reflexivity
    for a_name in archetypes:
        assert precedes(a_name, a_name), f"Reflexivity failed for {a_name}"

    # Transitivity
    for a1_name in archetypes:
        for a2_name in archetypes:
            for a3_name in archetypes:
                if precedes(a1_name, a2_name) and precedes(a2_name, a3_name):
                    assert precedes(a1_name, a3_name), f"Transitivity failed for {a1_name}, {a2_name}, {a3_name}"

    # Antisymmetry
    for a1_name in archetypes:
        for a2_name in archetypes:
            if precedes(a1_name, a2_name) and precedes(a2_name, a1_name):
                assert a1_name == a2_name, f"Antisymmetry failed for {a1_name}, {a2_name}"

    # Canonical chain
    chain_pairs = [
        ("fieldCorrelator", "detectorProjector"),
        ("detectorProjector", "modeNullspace"),
        ("modeNullspace", "rankHierarchy"),
        ("rankHierarchy", "scaleInvariantObservable")
    ]
    for p1, p2 in chain_pairs:
        assert precedes(p1, p2), f"Chain step {p1} <= {p2} failed"
        assert ranks[p2] == ranks[p1] + 1, f"Chain step {p1} -> {p2} not successor (+1)"

    def matrix_to_int_list(m: sp.Matrix) -> List[List[int]]:
        return [[int(m[i, j]) for j in range(m.cols)] for i in range(m.rows)]

    # Build certificate dictionary
    certificate = {
        "metadata": {
            "module": "DetectorGeometry.FieldCorrelatorProjection",
            "cas_engine": f"SymPy {sp.__version__}",
            "verified_invariants_count": 5
        },
        "field_correlator": {
            "single_projector_linear": True,
            "single_projector_lhs": str(lhs_single),
            "single_projector_rhs": str(rhs_single),
            "pair_projector_bilinear_scale": True,
            "pair_projector_lhs": str(lhs_pair),
            "pair_projector_rhs": str(rhs_pair),
            "kronecker_factorization_verified": True
        },
        "mode_projection": {
            "oscillatory_modes_annihilated": True,
            "mode_trace_linear": True,
            "projection_algebra": {
                "Pi_0": matrix_to_int_list(Pi_0),
                "Pi_1": matrix_to_int_list(Pi_1),
                "idempotent_0": True,
                "idempotent_1": True,
                "orthogonal": True,
                "complete": True,
                "annihilates_oscillatory": True
            }
        },
        "rank_hierarchy": {
            "singles_count_degree": 1,
            "coincidence_count_degree": 2,
            "parabola_identity_verified": True,
            "scale_invariant_ratio": str(ratio),
            "ratio_independent_of_X": True
        },
        "causal_poset": {
            "archetypes": archetypes,
            "ranks": ranks,
            "step_deltas": deltas,
            "strictly_monotonic": True,
            "injective": True,
            "poset_axioms": {
                "reflexive": True,
                "transitive": True,
                "antisymmetric": True
            },
            "canonical_chain_steps": [
                {"precedes": f"{p1} <= {p2}", "rank_lhs": int(ranks[p1]), "rank_rhs": int(ranks[p2]), "delta": int(ranks[p2] - ranks[p1])}
                for p1, p2 in chain_pairs
            ]
        },
        "lean_mapping": {
            "projector_single_linear": "dsimp [projectSingle]; rw [mul_add, mul_left_comm ...]",
            "projector_pair_bilinear_scale": "mul_mul_mul_comm eps1 eps2 a b",
            "oscillatory_modes_annihilated": "dsimp [modeTrace]; rw [MulZeroClass.zero_mul, AddMonoid.add_zero]",
            "modeTrace_linear": "dsimp [modeTrace]; repeat rw [MulZeroClass.zero_mul, AddMonoid.add_zero]",
            "coincidence_is_rank_two": "rfl",
            "square_root_coordinate_is_linear": "rfl",
            "detector_projection_parabola": "coincidence_is_rank_two N0 K X",
            "rank_inj": "intro a b h; cases a <;> cases b <;> first | rfl | contradiction",
            "causal_antisymm": "rank_inj (Nat.le_antisymm hab hba)",
            "canonical_chain": "⟨Nat.le_succ 195, Nat.le_succ 196, Nat.le_succ 197, Nat.le_succ 198⟩"
        }
    }

    out_path = os.path.join(os.path.dirname(__file__), "certificate.json")
    with open(out_path, "w") as f:
        json.dump(certificate, f, indent=2)
    print(f"Successfully wrote certificate to {out_path}")
    print("All 5 FieldCorrelatorProjection invariant classes verified with SymPy.")
    return certificate

if __name__ == "__main__":
    generate_field_correlator_certificates()
