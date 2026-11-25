/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Canonical.NeutralDualPairSplitting
import InfoGeometry.Twistor.RealTwistorIncidence
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Real skew incidence in the native neutral carrier

The graph of an evaluation-skew map `E* → E` is its own neutral orthogonal
complement. Opposite graphs have cross-pairing `2 η (P ξ)`. The real linear
mirror negates the primal coordinate and fixes the dual coordinate; its fixed
states in the graph are precisely the kernel covectors.

The matrix realization uses the native `dotProductEquiv`. Its rectangular
congruence is the actual composite `Q ∘ P ∘ Q.dualMap`. These algebraic facts
do not assert Courant bracket closure, global Casimir functions, or physical CPT.
-/

noncomputable section

namespace InfoGeometry.Clifford.NeutralSkewIncidence

open Matrix
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Canonical.NeutralDualPairSplitting
open InfoGeometry.Twistor.RealTwistorIncidence

section Native

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- The real primal-sign mirror on the existing neutral carrier. -/
def diracMirror : Module.End ℝ (PhaseSpaceCarrier E) := -neutralParaInvolution

@[simp] theorem diracMirror_apply (z : PhaseSpaceCarrier E) :
    diracMirror z = (-z.1, z.2) := by
  simp [diracMirror, neutralParaInvolution_apply]

theorem diracMirror_involutive : Function.Involutive (diracMirror (E := E)) := by
  rintro ⟨u, ξ⟩
  simp only [diracMirror_apply, neg_neg]

/-- The neutral form changes sign when both arguments are mirrored. -/
theorem diracMirror_anti_isometry (z w : PhaseSpaceCarrier E) :
    canonicalNeutralBilin (diracMirror z) (diracMirror w) =
      -canonicalNeutralBilin z w := by
  simp only [canonicalNeutralBilin_apply, diracMirror_apply, map_neg]
  ring

@[simp] theorem diracMirror_incidenceMap
    (P : Module.Dual ℝ E →ₗ[ℝ] E) (ξ : Module.Dual ℝ E) :
    diracMirror (incidenceMap P ξ) = incidenceMap (-P) ξ := by
  simp only [diracMirror_apply, incidenceMap_apply, LinearMap.neg_apply]

/-- The mirror exchanges the two native incidence submodules. -/
theorem diracMirror_incidenceSpace (P : Module.Dual ℝ E →ₗ[ℝ] E) :
    (incidenceSpace P).map diracMirror = incidenceSpace (-P) := by
  ext z
  constructor
  · rintro ⟨w, ⟨ξ, rfl⟩, rfl⟩
    exact ⟨ξ, (diracMirror_incidenceMap P ξ).symm⟩
  · rintro ⟨ξ, rfl⟩
    exact ⟨incidenceMap P ξ, ⟨ξ, rfl⟩, diracMirror_incidenceMap P ξ⟩

/-- Mirror-fixed neutral states have zero primal coordinate. -/
theorem diracMirror_fixed_iff (z : PhaseSpaceCarrier E) :
    diracMirror z = z ↔ z.1 = 0 := by
  constructor
  · intro h
    have hx : -z.1 = z.1 := by
      simpa only [diracMirror_apply] using congrArg Prod.fst h
    apply (Module.forall_dual_apply_eq_zero_iff ℝ z.1).mp
    intro ξ
    have hξ := congrArg ξ hx
    simp only [map_neg] at hξ
    linarith
  · intro h
    apply Prod.ext
    · simp only [diracMirror_apply, h, neg_zero]
    · simp only [diracMirror_apply]

/-- This fixed-state characterization needs no skewness assumption. -/
theorem diracMirror_incidence_fixed_iff
    (P : Module.Dual ℝ E →ₗ[ℝ] E) (ξ : Module.Dual ℝ E) :
    diracMirror (incidenceMap P ξ) = incidenceMap P ξ ↔ P ξ = 0 := by
  exact diracMirror_fixed_iff (incidenceMap P ξ)

/-- Opposite-graph intersections are exactly zero primal coordinate and kernel
dual coordinate; this also needs no skewness assumption. -/
theorem mem_opposite_incidence_iff
    (P : Module.Dual ℝ E →ₗ[ℝ] E) (z : PhaseSpaceCarrier E) :
    z ∈ incidenceSpace P ⊓ incidenceSpace (-P) ↔ z.1 = 0 ∧ P z.2 = 0 := by
  simp only [Submodule.mem_inf, mem_incidenceSpace, LinearMap.neg_apply]
  constructor
  · rintro ⟨hP, hneg⟩
    have hfix : diracMirror z = z := by
      apply Prod.ext
      · change -z.1 = z.1
        rw [hP]
        exact hneg.symm.trans hP
      · simp only [diracMirror_apply]
    have hz := (diracMirror_fixed_iff z).mp hfix
    exact ⟨hz, hP.symm.trans hz⟩
  · rintro ⟨hz, hP⟩
    simp only [hz, hP, neg_zero, and_self]

theorem incidenceMap_mem_opposite_iff
    (P : Module.Dual ℝ E →ₗ[ℝ] E) (ξ : Module.Dual ℝ E) :
    incidenceMap P ξ ∈ incidenceSpace P ⊓ incidenceSpace (-P) ↔ P ξ = 0 := by
  simp only [mem_opposite_incidence_iff, incidenceMap_apply, and_self]

/-- Kernel-fixed states are precisely the intersection states within a graph. -/
theorem incidence_fixed_iff_intersection
    (P : Module.Dual ℝ E →ₗ[ℝ] E) (ξ : Module.Dual ℝ E) :
    diracMirror (incidenceMap P ξ) = incidenceMap P ξ ↔
      incidenceMap P ξ ∈ incidenceSpace P ⊓ incidenceSpace (-P) := by
  rw [diracMirror_incidence_fixed_iff, incidenceMap_mem_opposite_iff]

/-- Same-graph neutral pairings vanish for evaluation-skew operators. -/
theorem incidence_isotropic (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (hP : ∀ ξ η : Module.Dual ℝ E, ξ (P η) = -η (P ξ))
    (ξ η : Module.Dual ℝ E) :
    canonicalNeutralBilin (incidenceMap P ξ) (incidenceMap P η) = 0 := by
  simp only [canonicalNeutralBilin_apply, incidenceMap_apply]
  rw [hP ξ η]
  exact neg_add_cancel _

/-- The sign is determined by the ordered positive-negative graph convention. -/
theorem incidence_cross_pairing (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (hP : ∀ ξ η : Module.Dual ℝ E, ξ (P η) = -η (P ξ))
    (ξ η : Module.Dual ℝ E) :
    canonicalNeutralBilin (incidenceMap P ξ) (incidenceMap (-P) η) =
      2 * η (P ξ) := by
  simp only [canonicalNeutralBilin_apply, incidenceMap_apply, LinearMap.neg_apply, map_neg]
  rw [hP ξ η]
  ring

/-- The graph equals its neutral orthogonal set; no finite dimension is needed. -/
theorem incidence_etaOrthogonal (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (hP : ∀ ξ η : Module.Dual ℝ E, ξ (P η) = -η (P ξ)) :
    etaOrthogonal (incidenceSpace P) =
      (incidenceSpace P : Set (PhaseSpaceCarrier E)) := by
  ext z
  constructor
  · intro hz
    apply (mem_incidenceSpace P z).mpr
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff ℝ (z.1 - P z.2)).mp
    intro η
    have h := hz (incidenceMap P η) ⟨η, rfl⟩
    simp only [canonicalNeutralBilin_apply, incidenceMap_apply] at h
    rw [hP z.2 η] at h
    simp only [map_sub]
    linarith
  · rintro ⟨ξ, rfl⟩ w ⟨η, rfl⟩
    exact incidence_isotropic P hP ξ η

/-- Equality also holds for Mathlib's native orthogonal submodule. -/
theorem incidence_orthogonal (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (hP : ∀ ξ η : Module.Dual ℝ E, ξ (P η) = -η (P ξ)) :
    canonicalNeutralBilin.orthogonal (incidenceSpace P) = incidenceSpace P := by
  ext z
  have h := Set.ext_iff.mp (incidence_etaOrthogonal P hP) z
  simpa only [LinearMap.BilinForm.mem_orthogonal_iff, etaOrthogonal,
    Set.mem_ofPred_eq, SetLike.mem_coe, canonicalNeutralBilin_apply, add_comm] using h

/-- Any totally isotropic submodule containing the graph equals the graph. -/
theorem incidence_maximal_isotropic (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (hP : ∀ ξ η : Module.Dual ℝ E, ξ (P η) = -η (P ξ))
    (W : Submodule ℝ (PhaseSpaceCarrier E)) (hPW : incidenceSpace P ≤ W)
    (hW : ∀ z ∈ W, ∀ w ∈ W, canonicalNeutralBilin z w = 0) :
    W = incidenceSpace P := by
  refine le_antisymm ?_ hPW
  intro z hz
  have hzorth : z ∈ etaOrthogonal (incidenceSpace P) := by
    intro w hw
    exact hW z hz w (hPW hw)
  rw [incidence_etaOrthogonal P hP] at hzorth
  exact hzorth

/-- Native pullback/pushforward preserves the evaluation-skew law. -/
theorem dual_congruence_skew (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (hP : ∀ ξ η : Module.Dual ℝ E, ξ (P η) = -η (P ξ)) (Q : E →ₗ[ℝ] F) :
    ∀ ξ η : Module.Dual ℝ F,
      ξ ((Q.comp (P.comp Q.dualMap)) η) =
        -η ((Q.comp (P.comp Q.dualMap)) ξ) := by
  intro ξ η
  exact hP (Q.dualMap ξ) (Q.dualMap η)

/-- A pulled-back kernel covector remains in the coarse kernel. -/
theorem dual_congruence_kernel (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (Q : E →ₗ[ℝ] F) (ξ : Module.Dual ℝ F) (hξ : P (Q.dualMap ξ) = 0) :
    (Q.comp (P.comp Q.dualMap)) ξ = 0 := by
  simp only [LinearMap.comp_apply, hξ, map_zero]

end Native

section Matrices

variable {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

/-- A real matrix as a map from the genuine algebraic dual, via dot product. -/
def matrixSharp (P : Matrix n n ℝ) : Module.Dual ℝ (n → ℝ) →ₗ[ℝ] (n → ℝ) :=
  P.mulVecLin.comp (dotProductEquiv ℝ n).symm.toLinearMap

@[simp] theorem matrixSharp_apply (P : Matrix n n ℝ) (u : n → ℝ) :
    matrixSharp P (dotProductEquiv ℝ n u) = P *ᵥ u := by
  simp only [matrixSharp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Matrix.mulVecLin_apply]

@[simp] theorem matrixSharp_neg (P : Matrix n n ℝ) :
    matrixSharp (-P) = -matrixSharp P := by
  apply LinearMap.ext
  intro ξ
  simp only [matrixSharp, LinearMap.comp_apply, Matrix.mulVecLin_apply,
    LinearMap.neg_apply, neg_mulVec]

theorem matrixSharp_add (P R : Matrix n n ℝ) :
    matrixSharp (P + R) = matrixSharp P + matrixSharp R := by
  apply LinearMap.ext
  intro ξ
  simp only [matrixSharp, LinearMap.comp_apply, Matrix.mulVecLin_apply,
    LinearMap.add_apply, add_mulVec]

/-- Transpose-skew matrices induce evaluation-skew maps on the genuine dual. -/
theorem matrixSharp_skew (P : Matrix n n ℝ) (hP : Pᵀ = -P) :
    ∀ ξ η : Module.Dual ℝ (n → ℝ), ξ (matrixSharp P η) = -η (matrixSharp P ξ) := by
  intro ξ η
  obtain ⟨u, rfl⟩ := (dotProductEquiv ℝ n).surjective ξ
  obtain ⟨v, rfl⟩ := (dotProductEquiv ℝ n).surjective η
  simp only [matrixSharp_apply, dotProductEquiv_apply_apply]
  calc
    u ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (Pᵀ *ᵥ u) := (dotProduct_transpose_mulVec P v u).symm
    _ = -(v ⬝ᵥ (P *ᵥ u)) := by rw [hP, neg_mulVec, dotProduct_neg]

/-- Matrix coordinates preserve the ordered native cross-pairing. -/
theorem matrix_incidence_cross_pairing (P : Matrix n n ℝ) (hP : Pᵀ = -P)
    (u v : n → ℝ) :
    canonicalNeutralBilin
        (incidenceMap (matrixSharp P) (dotProductEquiv ℝ n u))
        (incidenceMap (matrixSharp (-P)) (dotProductEquiv ℝ n v)) =
      2 * (v ⬝ᵥ (P *ᵥ u)) := by
  rw [matrixSharp_neg, incidence_cross_pairing _ (matrixSharp_skew P hP)]
  simp only [matrixSharp_apply, dotProductEquiv_apply_apply]

/-- Dual pullback by a matrix is multiplication by its transpose in these coordinates. -/
theorem mulVecLin_dualMap_dotProduct (Q : Matrix m n ℝ) (u : m → ℝ) :
    Q.mulVecLin.dualMap (dotProductEquiv ℝ m u) =
      dotProductEquiv ℝ n (Qᵀ *ᵥ u) := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.dualMap_apply, Matrix.mulVecLin_apply,
    dotProductEquiv_apply_apply]
  calc
    u ⬝ᵥ (Q *ᵥ v) = v ⬝ᵥ (Qᵀ *ᵥ u) := (dotProduct_transpose_mulVec Q v u).symm
    _ = (Qᵀ *ᵥ u) ⬝ᵥ v := dotProduct_comm _ _

/-- Rectangular matrix congruence is the native primal/dual composite. -/
theorem matrixSharp_congruence (Q : Matrix m n ℝ) (P : Matrix n n ℝ) :
    matrixSharp (Q * P * Qᵀ) =
      Q.mulVecLin.comp ((matrixSharp P).comp Q.mulVecLin.dualMap) := by
  apply LinearMap.ext
  intro ξ
  obtain ⟨u, rfl⟩ := (dotProductEquiv ℝ m).surjective ξ
  simp only [matrixSharp_apply, LinearMap.comp_apply, mulVecLin_dualMap_dotProduct,
    Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]

end Matrices

end InfoGeometry.Clifford.NeutralSkewIncidence
