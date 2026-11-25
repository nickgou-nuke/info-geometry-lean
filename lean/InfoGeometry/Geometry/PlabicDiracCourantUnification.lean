/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.DiracGraphMirror
import InfoGeometry.Geometry.MatrixDiracGraphs
import InfoGeometry.Topology.AmplituhedronGeneralTwistorExpansion
import InfoGeometry.Canonical.FinitePlabicKasteleyn

/-!
# Neutral graph contractions, real spinor minors, and finite bipartite networks

This file connects the existing neutral graph submodules to real two-dimensional
minors and to the existing finite bipartite edge-sum operators. The chosen
epsilon matrix sends `(a₀,a₁)` to `(a₁,-a₀)`, so a half white-black contraction
is MINUS the determinant bracket. The common sign cancels in the quadratic
Plücker relation.

All statements concern linear algebra or supplied finite graph data. No planar
embedding, Courant integrability, physical CPT action, entropy function, or
spin-network intertwiner is constructed. Matrix congruence is identified with
the forward image of a linear graph relation, without a rank assumption.
-/

noncomputable section

namespace InfoGeometry.Geometry.PlabicDiracCourantUnification

open Matrix
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Geometry.SkewGraphNeutralPairing
open InfoGeometry.Geometry.MatrixDiracGraphs
open InfoGeometry.Geometry.DiracGraphMirror
open InfoGeometry.Amplituhedron
open InfoGeometry.Canonical.FinitePlabicKasteleyn

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A chosen graph state: true is the positive sector, false the negative sector. -/
def sectorState (P : Matrix ι ι ℝ) (positive : Bool) (a : ι → ℝ) :
    PhaseSpaceCarrier (ι → ℝ) :=
  if positive then coordinatePhase (P *ᵥ a, a)
  else coordinatePhase (-(P *ᵥ a), a)

/-- The mirror exchanges the two chosen sectors, even when the graph map is not skew. -/
theorem diracMirror_sectorState (P : Matrix ι ι ℝ) (c : Bool) (a : ι → ℝ) :
    diracMirror (sectorState P c a) = sectorState P (!c) a := by
  cases c <;> simp [sectorState, coordinatePhase_apply, diracMirror_apply]

/-- The same-sector contraction vanishes for a skew graph map. -/
theorem same_sector_pair_zero (P : Matrix ι ι ℝ) (hP : Pᵀ = -P)
    (c : Bool) (a b : ι → ℝ) :
    canonicalNeutralBilin (sectorState P c a) (sectorState P c b) = 0 := by
  cases c
  · exact matrix_neg_graph_isotropic P hP a b
  · exact (matrix_graph_vectors_isotropic_iff P).mpr hP a b

/-- Nonzero contractions between sector-labelled states have opposite colors.
This is a selection rule for the specified pairing, independent of planarity. -/
theorem nonzero_pair_opposite_sectors (P : Matrix ι ι ℝ) (hP : Pᵀ = -P)
    (c d : Bool) (a b : ι → ℝ)
    (h : canonicalNeutralBilin (sectorState P c a) (sectorState P d b) ≠ 0) :
    c ≠ d := by
  intro hcd
  subst d
  exact h (same_sector_pair_zero P hP c a b)

/-- The positive-negative graph contraction in the half-neutral normalization. -/
def halfCrossPair (P : Matrix ι ι ℝ) (a b : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) * canonicalNeutralBilin
    (coordinatePhase (P *ᵥ a, a)) (coordinatePhase (-(P *ᵥ b), b))

theorem halfCrossPair_eq_dot (P : Matrix ι ι ℝ) (hP : Pᵀ = -P)
    (a b : ι → ℝ) : halfCrossPair P a b = dotProduct (P *ᵥ a) b := by
  rw [halfCrossPair, matrix_graph_cross_pair P hP]
  ring

/-! ## Matrix transport and addition -/

omit [Fintype ι] [DecidableEq ι] in
theorem skew_add (P R : Matrix ι ι ℝ) (hP : Pᵀ = -P) (hR : Rᵀ = -R) :
    (P + R)ᵀ = -(P + R) := by
  rw [Matrix.transpose_add, hP, hR, neg_add]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Rectangular congruence preserves skewness; no invertibility is required. -/
theorem skew_congruence (P : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ)
    (hP : Pᵀ = -P) : (Q * P * Qᵀ)ᵀ = -(Q * P * Qᵀ) := by
  calc
    (Q * P * Qᵀ)ᵀ = Q * (Pᵀ * Qᵀ) := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = -(Q * P * Qᵀ) := by
      rw [hP, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

/-- Congruence is precisely the forward image of the graph relation.
The covector pulls back by the transpose while the primal vector pushes forward. -/
theorem matrix_graph_forward_image (P : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ)
    (w η : κ → ℝ) :
    (∃ u : ι → ℝ,
      coordinatePhase (u, Qᵀ *ᵥ η) ∈ dualGraph (matrixSharp P) ∧ w = Q *ᵥ u) ↔
      coordinatePhase (w, η) ∈ dualGraph (matrixSharp (Q * P * Qᵀ)) := by
  simp only [coordinatePhase_mem_dualGraph_iff]
  constructor
  · rintro ⟨u, hu, hw⟩
    rw [hw, hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  · intro hw
    refine ⟨P *ᵥ (Qᵀ *ᵥ η), rfl, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact hw

omit [DecidableEq ι] [DecidableEq κ] in
/-- A pulled-back kernel covector remains a kernel covector after congruence.
The converse is not asserted for a noninjective transfer map. -/
theorem congruence_kernel_of_pullback (P : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ)
    (η : κ → ℝ) (h : P *ᵥ (Qᵀ *ᵥ η) = 0) :
    (Q * P * Qᵀ) *ᵥ η = 0 := by
  calc
    (Q * P * Qᵀ) *ᵥ η = Q *ᵥ (P *ᵥ (Qᵀ *ᵥ η)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = 0 := by rw [h, Matrix.mulVec_zero]

/-- Shared kernel directions lie in both opposite graphs of the sum.
This algebraic inclusion needs no skewness assumption. -/
theorem shared_kernel_mem_sum_graphs (P R : Matrix ι ι ℝ) (ξ : ι → ℝ)
    (hP : P *ᵥ ξ = 0) (hR : R *ᵥ ξ = 0) :
    coordinatePhase (0, ξ) ∈
      dualGraph (matrixSharp (P + R)) ⊓ dualGraph (-matrixSharp (P + R)) := by
  rw [mem_dualGraph_inf_neg]
  simp [coordinatePhase_apply, matrixSharp_apply_dotProductEquiv,
    Matrix.add_mulVec, hP, hR]

/-! ## Real two-dimensional specialization -/

def eps2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

theorem eps2_skew : eps2ᵀ = -eps2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps2]

/-- The real spinor bracket is a specialization of the existing two-row minor. -/
def spinorBracket (a b : Fin 2 → ℝ) : ℝ :=
  minor2 (!![a 0, b 0; a 1, b 1]) 0 1

@[simp] theorem spinorBracket_apply (a b : Fin 2 → ℝ) :
    spinorBracket a b = a 0 * b 1 - a 1 * b 0 := rfl

/-- The sign is negative for the displayed epsilon matrix and sector order. -/
theorem halfCrossPair_eps2 (a b : Fin 2 → ℝ) :
    halfCrossPair eps2 a b = -spinorBracket a b := by
  rw [halfCrossPair_eq_dot eps2 eps2_skew, spinorBracket_apply]
  simp [eps2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- A concrete counterexample to the positive sign in the submitted proposal. -/
theorem eps2_orientation_witness :
    halfCrossPair eps2 ![1, 0] ![0, 1] = -1 ∧
      spinorBracket ![1, 0] ![0, 1] = 1 := by
  simp [halfCrossPair_eps2]

/-- The existing Plücker theorem transported to arbitrary families of real spinors. -/
theorem spinorBracket_plucker {n : ℕ} (spinors : Fin n → Fin 2 → ℝ)
    (a b c d : Fin n) :
    spinorBracket (spinors a) (spinors c) * spinorBracket (spinors b) (spinors d) =
      spinorBracket (spinors a) (spinors b) * spinorBracket (spinors c) (spinors d) +
      spinorBracket (spinors a) (spinors d) * spinorBracket (spinors b) (spinors c) := by
  simpa only [spinorBracket_apply, minor2] using
    plucker_relation_general (fun r j => spinors j r) a b c d

/-- Both sign factors cancel in each product, so the cross-pairings obey Plücker. -/
theorem halfCrossPair_eps2_plucker {n : ℕ} (spinors : Fin n → Fin 2 → ℝ)
    (a b c d : Fin n) :
    halfCrossPair eps2 (spinors a) (spinors c) * halfCrossPair eps2 (spinors b) (spinors d) =
      halfCrossPair eps2 (spinors a) (spinors b) * halfCrossPair eps2 (spinors c) (spinors d) +
      halfCrossPair eps2 (spinors a) (spinors d) * halfCrossPair eps2 (spinors b) (spinors c) := by
  simp only [halfCrossPair_eps2, neg_mul_neg]
  exact spinorBracket_plucker spinors a b c d

theorem eps2_mulVec_eq_zero_iff (a : Fin 2 → ℝ) : eps2 *ᵥ a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    have ha₁ : a 1 = 0 := by
      simpa [eps2, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h₀
    have ha₀ : a 0 = 0 := by
      simpa [eps2, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h₁
    ext i
    fin_cases i <;> simp [ha₀, ha₁]
  · rintro rfl
    exact Matrix.mulVec_zero _

/-- In the nondegenerate epsilon graph the only mirror-fixed state is zero. -/
theorem eps2_graph_fixed_iff_zero (v : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    (coordinatePhase v ∈ dualGraph (matrixSharp eps2) ∧
      diracMirror (coordinatePhase v) = coordinatePhase v) ↔ v = 0 := by
  rw [mem_dualGraph_and_fixed_iff]
  simp only [coordinatePhase_apply, matrixSharp_apply_dotProductEquiv,
    eps2_mulVec_eq_zero_iff]
  simp [Prod.ext_iff]

/-! ## Actual finite bipartite edge-sum operators -/

/-- Edge weight from the neutral pairing of the supplied endpoint graph states. -/
def contractionWeight (G : FinitePlabicGraph) (P : Matrix ι ι ℝ)
    (white : G.White → ι → ℝ) (black : G.Black → ι → ℝ) (e : G.Edge) : ℝ :=
  canonicalNeutralBilin
    (coordinatePhase (P *ᵥ white (G.whiteEndpoint e), white (G.whiteEndpoint e)))
    (coordinatePhase (-(P *ᵥ black (G.blackEndpoint e)), black (G.blackEndpoint e)))

theorem contractionWeight_eq_dot (G : FinitePlabicGraph) (P : Matrix ι ι ℝ)
    (hP : Pᵀ = -P) (white : G.White → ι → ℝ) (black : G.Black → ι → ℝ)
    (e : G.Edge) :
    contractionWeight G P white black e =
      2 * dotProduct (P *ᵥ white (G.whiteEndpoint e)) (black (G.blackEndpoint e)) :=
  matrix_graph_cross_pair P hP _ _

theorem contractionWeight_eps2 (G : FinitePlabicGraph)
    (white : G.White → Fin 2 → ℝ) (black : G.Black → Fin 2 → ℝ) (e : G.Edge) :
    contractionWeight G eps2 white black e =
      (-2 : ℝ) * spinorBracket (white (G.whiteEndpoint e)) (black (G.blackEndpoint e)) := by
  have h := halfCrossPair_eps2 (white (G.whiteEndpoint e)) (black (G.blackEndpoint e))
  change (1 / 2 : ℝ) * contractionWeight G eps2 white black e = _ at h
  linarith

/-- The real signed edge matrix differs from the determinant-bracket one by -2. -/
theorem edgeSumMatrix_eps2 (G : FinitePlabicGraph) (S : KasteleynSigning G)
    (white : G.White → Fin 2 → ℝ) (black : G.Black → Fin 2 → ℝ) :
    edgeSumMatrix S (contractionWeight G eps2 white black) =
      (-2 : ℝ) • edgeSumMatrix S
        (fun e => spinorBracket (white (G.whiteEndpoint e)) (black (G.blackEndpoint e))) := by
  change edgeSumMatrix S (fun e => contractionWeight G eps2 white black e) = _
  simp_rw [contractionWeight_eps2]
  exact edgeSumMatrix_smul S (-2) _

/-- The existing block Dirac operator has the same real scaling. -/
theorem edgeSumDirac_eps2 (G : FinitePlabicGraph) (S : KasteleynSigning G)
    (white : G.White → Fin 2 → ℝ) (black : G.Black → Fin 2 → ℝ) :
    edgeSumDirac S (contractionWeight G eps2 white black) =
      (-2 : ℝ) • edgeSumDirac S
        (fun e => spinorBracket (white (G.whiteEndpoint e)) (black (G.blackEndpoint e))) := by
  change edgeSumDirac S (fun e => contractionWeight G eps2 white black e) = _
  simp_rw [contractionWeight_eps2]
  exact edgeSumDirac_smul S (-2) (by simp) _

end InfoGeometry.Geometry.PlabicDiracCourantUnification
