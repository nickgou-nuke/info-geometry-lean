/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic.Positivity

/-!
# Positive Dirichlet operators from bounded Hilbert-space maps

The operator is the actual sum of adjoint compositions. Its quadratic form
and kernel are derived from that construction on arbitrary complex Hilbert
spaces; neither positivity nor a gap is stored as a certificate.
-/

noncomputable section

open scoped BigOperators InnerProductSpace
open ContinuousLinearMap

namespace InfoGeometry.Analysis.OperatorDirichletLaplacian

variable {ι E F : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The native sum of squared bounded maps, acting on the common domain. -/
def laplacian (T : ι → E →L[ℂ] F) : E →L[ℂ] E :=
  ∑ i, (adjoint (T i)).comp (T i)

/-- The squared image norms of the family. -/
def energy (T : ι → E →L[ℂ] F) (x : E) : ℝ :=
  ∑ i, ‖T i x‖ ^ 2

omit [CompleteSpace E] [CompleteSpace F] in
theorem energy_nonneg (T : ι → E →L[ℂ] F) (x : E) : 0 ≤ energy T x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The Dirichlet form is the exact Hilbert quadratic of the constructed operator. -/
theorem re_inner_laplacian (T : ι → E →L[ℂ] F) (x : E) :
    (inner ℂ x (laplacian T x)).re = energy T x := by
  simp [laplacian, energy, inner_sum, adjoint_inner_right,
    inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

theorem isPositive_laplacian (T : ι → E →L[ℂ] F) :
    (laplacian T).IsPositive := by
  exact isPositive_sum Finset.univ fun i _ => isPositive_adjoint_comp_self (T i)

theorem isSelfAdjoint_laplacian (T : ι → E →L[ℂ] F) :
    IsSelfAdjoint (laplacian T) := (isPositive_laplacian T).isSelfAdjoint

omit [CompleteSpace E] [CompleteSpace F] in
theorem energy_eq_zero_iff (T : ι → E →L[ℂ] F) (x : E) :
    energy T x = 0 ↔ ∀ i, T i x = 0 := by
  simp only [energy, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖T i x‖),
    Finset.mem_univ, forall_true_left, sq_eq_zero_iff, norm_eq_zero]

/-- The kernel contains exactly the simultaneous zero vectors of the original maps. -/
theorem laplacian_apply_eq_zero_iff (T : ι → E →L[ℂ] F) (x : E) :
    laplacian T x = 0 ↔ ∀ i, T i x = 0 := by
  constructor
  · intro h
    apply (energy_eq_zero_iff T x).mp
    rw [← re_inner_laplacian, h, inner_zero_right, Complex.zero_re]
  · intro h
    simp [laplacian, h]

/-- Equality of native submodules, not only a scalar zero-energy test. -/
theorem ker_laplacian (T : ι → E →L[ℂ] F) :
    (laplacian T).ker = ⨅ i, (T i).ker := by
  ext x
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Submodule.mem_iInf, laplacian_apply_eq_zero_iff]

omit [CompleteSpace E] [CompleteSpace F] in
theorem energy_pos_iff (T : ι → E →L[ℂ] F) (x : E) :
    0 < energy T x ↔ ∃ i, T i x ≠ 0 := by
  rw [lt_iff_le_and_ne, and_iff_right (energy_nonneg T x), ne_comm]
  simp only [Ne, energy_eq_zero_iff, not_forall]

omit [CompleteSpace E] [CompleteSpace F] in
theorem energy_smul (T : ι → E →L[ℂ] F) (c : ℂ) (x : E) :
    energy T (c • x) = ‖c‖ ^ 2 * energy T x := by
  simp [energy, norm_smul, mul_pow, Finset.mul_sum]

omit [CompleteSpace E] [CompleteSpace F] in
theorem energy_smul_real (T : ι → E →L[ℂ] F) (r : ℝ) (x : E) :
    energy T (r • x) = r ^ 2 * energy T x := by
  simpa using energy_smul T (r : ℂ) x

/-- Scaling the maps scales their actual operator square quadratically. -/
theorem laplacian_smul_real (T : ι → E →L[ℂ] F) (r : ℝ) :
    laplacian (fun i => r • T i) = (r * r) • laplacian T := by
  have hreal (S : E →L[ℂ] F) : adjoint (r • S) = r • adjoint S := by
    simpa using (adjoint : (E →L[ℂ] F) ≃ₗᵢ⋆[ℂ] (F →L[ℂ] E)).map_smulₛₗ (r : ℂ) S
  simp [laplacian, hreal, smul_comp, comp_smul, smul_smul, Finset.smul_sum]

omit [CompleteSpace E] [CompleteSpace F] in
theorem energy_family_smul_real (T : ι → E →L[ℂ] F) (r : ℝ) (x : E) :
    energy (fun i => r • T i) x = r ^ 2 * energy T x := by
  simp [energy, norm_smul, mul_pow, Finset.mul_sum]

/-- A native unitary of the operator algebra transports the constructed Laplacian. -/
theorem laplacian_unitary_conjugate (T : ι → E →L[ℂ] E)
    (u : unitary (E →L[ℂ] E)) :
    laplacian (fun i => (u : E →L[ℂ] E) * T i * (star u : E →L[ℂ] E)) =
      (u : E →L[ℂ] E) * laplacian T * (star u : E →L[ℂ] E) := by
  simp only [laplacian, ← ContinuousLinearMap.mul_def, ← star_eq_adjoint]
  simpa only [map_mul, map_star, Unitary.conjStarAlgAut_apply] using
    (map_sum (Unitary.conjStarAlgAut ℂ (E →L[ℂ] E) u)
      (fun i => star (T i) * T i) Finset.univ).symm

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Pullback of a family gives conjugation of its Dirichlet operator by the actual adjoint. -/
theorem laplacian_precompose (T : ι → E →L[ℂ] F) (U : G →L[ℂ] E) :
    laplacian (fun i => (T i).comp U) =
      (adjoint U).comp ((laplacian T).comp U) := by
  ext x
  simp [laplacian, adjoint_comp, map_sum]

/-- An isometric change in the target preserves the full Dirichlet operator. -/
theorem laplacian_postcompose_isometry (T : ι → E →L[ℂ] F)
    (V : F →L[ℂ] G) (hV : Isometry V) :
    laplacian (fun i => V.comp (T i)) = laplacian T := by
  have h := V.isometry_iff_adjoint_comp_self.mp hV
  simp only [laplacian, adjoint_comp]
  apply Finset.sum_congr rfl
  intro i _
  calc
    ((adjoint (T i)).comp (adjoint V)).comp (V.comp (T i)) =
        (adjoint (T i)).comp (((adjoint V).comp V).comp (T i)) := by
      simp only [comp_assoc]
    _ = (adjoint (T i)).comp (T i) := by rw [h, one_def, id_comp]

/-- Unitary changes of both Hilbert carriers give genuine operator conjugation. -/
theorem laplacian_unitary_transport (T : ι → E →L[ℂ] F)
    (U : E ≃ₗᵢ[ℂ] E) (V : F ≃ₗᵢ[ℂ] F) :
    laplacian (fun i => (V : F →L[ℂ] F).comp
      ((T i).comp (U.symm : E →L[ℂ] E))) =
      (U : E →L[ℂ] E).comp ((laplacian T).comp (U.symm : E →L[ℂ] E)) := by
  rw [laplacian_postcompose_isometry _ _ V.isometry, laplacian_precompose]
  have hU : adjoint (U.symm : E →L[ℂ] E) = (U : E →L[ℂ] E) :=
    U.symm.adjoint_eq_symm
  rw [hU]

end InfoGeometry.Analysis.OperatorDirichletLaplacian
