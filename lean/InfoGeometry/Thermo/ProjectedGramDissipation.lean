/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import InfoGeometry.SuperMetriplectic.Flow
import Mathlib.Tactic.Linarith

/-!
# Energy-degenerate dissipation from projected Gram operators

On real Hilbert spaces, project away from the energy vector before applying
each actual operator. The sum of the resulting adjoint squares is symmetric,
positive, and annihilates the energy vector. Its kernel and strict-production
criterion are determined exactly by the projected operators.

The positive Hilbert metric is part of the carrier; an indefinite split norm
cannot substitute for it. The existing Onsager and metriplectic-flow types
are instantiated with proved laws. The final rate theorems are pointwise
operator statements with explicit reversible hypotheses. They assert no
Jacobi identity, existence of trajectories, Gibbs integrability, or heat bound.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Thermo.ProjectedGramDissipation

open scoped BigOperators
open InfoGeometry.SuperMetriplectic

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The actual ordered sum of adjoint squares after energy-orthogonal projection.
The native projection is defined even at a zero energy vector. -/
def projectedGram (R : ι → E →L[ℝ] F) (h : E) : E →L[ℝ] E :=
  ∑ i, ((R i).comp (ℝ ∙ h)ᗮ.starProjection).adjoint.comp
    ((R i).comp (ℝ ∙ h)ᗮ.starProjection)

/-- Keep the projection on both ordered sides of the unprojected Gram operator. -/
theorem projectedGram_eq_sandwich (R : ι → E →L[ℝ] F) (h : E) :
    projectedGram R h =
      ((ℝ ∙ h)ᗮ.starProjection.adjoint.comp
        (∑ i, (R i).adjoint.comp (R i))).comp (ℝ ∙ h)ᗮ.starProjection := by
  ext x
  simp only [projectedGram, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_comp, map_sum]

/-- The sum remains self-adjoint without any commutation hypothesis on the operators. -/
theorem projectedGram_adjoint (R : ι → E →L[ℝ] F) (h : E) :
    (projectedGram R h).adjoint = projectedGram R h := by
  simp only [projectedGram, map_sum, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- Exact bilinear readout of the full operator. -/
theorem projectedGram_pairing (R : ι → E →L[ℝ] F) (h x y : E) :
    inner ℝ x (projectedGram R h y) =
      ∑ i, inner ℝ (R i ((ℝ ∙ h)ᗮ.starProjection x))
        (R i ((ℝ ∙ h)ᗮ.starProjection y)) := by
  simp only [projectedGram, sum_apply, inner_sum,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

theorem projectedGram_pairing_symmetric (R : ι → E →L[ℝ] F) (h x y : E) :
    inner ℝ x (projectedGram R h y) = inner ℝ y (projectedGram R h x) := by
  simp only [projectedGram_pairing, real_inner_comm]

/-- Production is an actual finite sum of squared Hilbert norms. -/
theorem projectedGram_quadratic (R : ι → E →L[ℝ] F) (h x : E) :
    inner ℝ x (projectedGram R h x) =
      ∑ i, ‖R i ((ℝ ∙ h)ᗮ.starProjection x)‖ ^ 2 := by
  simp only [projectedGram_pairing, real_inner_self_eq_norm_sq]

theorem projectedGram_nonneg (R : ι → E →L[ℝ] F) (h x : E) :
    0 ≤ inner ℝ x (projectedGram R h x) := by
  rw [projectedGram_quadratic]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Energy degeneracy is constructed by the projection, including at h = 0. -/
theorem projectedGram_energy (R : ι → E →L[ℝ] F) (h : E) :
    projectedGram R h h = 0 := by
  simp only [projectedGram, sum_apply, ContinuousLinearMap.comp_apply,
    Submodule.starProjection_orthogonalComplement_singleton_eq_zero,
    map_zero, Finset.sum_const_zero]

/-- The metric bracket annihilates energy in its first argument as well. -/
theorem projectedGram_energy_pairing (R : ι → E →L[ℝ] F) (h x : E) :
    inner ℝ h (projectedGram R h x) = 0 := by
  rw [projectedGram_pairing_symmetric, projectedGram_energy, inner_zero_right]

/-- Vanishing production requires every projected operator to vanish on the vector. -/
theorem projectedGram_quadratic_eq_zero_iff (R : ι → E →L[ℝ] F) (h x : E) :
    inner ℝ x (projectedGram R h x) = 0 ↔
      ∀ i, R i ((ℝ ∙ h)ᗮ.starProjection x) = 0 := by
  rw [projectedGram_quadratic]
  constructor
  · intro hz i
    have hi : ‖R i ((ℝ ∙ h)ᗮ.starProjection x)‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hz i
        (Finset.mem_univ i)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro hz
    simp only [hz, norm_zero, zero_pow two_ne_zero, Finset.sum_const_zero]

/-- The operator kernel is exactly the intersection of the projected kernels. -/
theorem projectedGram_apply_eq_zero_iff (R : ι → E →L[ℝ] F) (h x : E) :
    projectedGram R h x = 0 ↔
      ∀ i, R i ((ℝ ∙ h)ᗮ.starProjection x) = 0 := by
  constructor
  · intro hx
    apply (projectedGram_quadratic_eq_zero_iff R h x).mp
    rw [hx, inner_zero_right]
  · intro hx
    simp only [projectedGram, sum_apply, ContinuousLinearMap.comp_apply, hx,
      map_zero, Finset.sum_const_zero]

/-- Strict production needs a nonzero projected channel; nonassociativity alone
does not establish that condition in an associator specialization. -/
theorem projectedGram_quadratic_pos_iff (R : ι → E →L[ℝ] F) (h x : E) :
    0 < inner ℝ x (projectedGram R h x) ↔
      ∃ i, R i ((ℝ ∙ h)ᗮ.starProjection x) ≠ 0 := by
  classical
  constructor
  · intro hp
    by_contra hn
    have hzall : ∀ i, R i ((ℝ ∙ h)ᗮ.starProjection x) = 0 := by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    have hz := (projectedGram_quadratic_eq_zero_iff R h x).mpr hzall
    linarith
  · rintro ⟨i, hi⟩
    have hn : inner ℝ x (projectedGram R h x) ≠ 0 := by
      intro hz
      exact hi ((projectedGram_quadratic_eq_zero_iff R h x).mp hz i)
    exact lt_of_le_of_ne (projectedGram_nonneg R h x) hn.symm

/-- Construct the existing Onsager data from the projected operators and a
nonnegative mobility, deriving its symmetry and positivity fields. -/
def projectedGramMetricData (R : ι → E →L[ℝ] F) (h : E)
    (γ : ℝ) (hγ : 0 ≤ γ) : OnsagerMetricData E where
  onsager := (γ • projectedGram R h).toLinearMap
  pairing := inner ℝ
  metric_symmetric := by
    intro x y
    change inner ℝ x (γ • projectedGram R h y) =
      inner ℝ y (γ • projectedGram R h x)
    rw [real_inner_smul_right, real_inner_smul_right, projectedGram_pairing_symmetric]
  metric_nonnegative := by
    intro x
    change 0 ≤ inner ℝ x (γ • projectedGram R h x)
    rw [real_inner_smul_right]
    exact mul_nonneg hγ (projectedGram_nonneg R h x)
  pairing_zero_right := inner_zero_right

/-- Instantiate the existing flow type with the actual dissipative operator.
The reversible map is unrestricted here; its rate hypotheses are stated below. -/
def projectedGramFlow (R : ι → E →L[ℝ] F) (h s : E) (J : E →L[ℝ] E)
    (γ : ℝ) (hγ : 0 ≤ γ) : MetriplecticFlow E where
  metric := projectedGramMetricData R h γ hγ
  entropyForce := s
  energyForce := h
  reversibleFlow := J h
  dissipativeFlow := (γ • projectedGram R h) s
  totalFlow := J h + (γ • projectedGram R h) s
  entropyProduction := γ * ∑ i, ‖R i ((ℝ ∙ h)ᗮ.starProjection s)‖ ^ 2
  dissipativeFlow_eq_onsager_entropy := rfl
  totalFlow_eq_reversible_add_dissipative := rfl
  energy_degeneracy := by
    change γ • projectedGram R h h = 0
    rw [projectedGram_energy, smul_zero]
  entropyProduction_eq_quadratic := by
    change γ * ∑ i, ‖R i ((ℝ ∙ h)ᗮ.starProjection s)‖ ^ 2 =
      inner ℝ s (γ • projectedGram R h s)
    rw [real_inner_smul_right, projectedGram_quadratic]

/-- Skew-adjoint reversible motion and the constructed degeneracy conserve energy. -/
theorem projectedGramFlow_energy_rate (R : ι → E →L[ℝ] F) (h s : E)
    (J : E →L[ℝ] E) (hJ : J.adjoint = -J) (γ : ℝ) (hγ : 0 ≤ γ) :
    inner ℝ h (projectedGramFlow R h s J γ hγ).totalFlow = 0 := by
  have hskew := ContinuousLinearMap.adjoint_inner_right J h h
  rw [hJ, neg_apply, inner_neg_right, real_inner_comm h (J h)]
    at hskew
  have hrev : inner ℝ h (J h) = 0 := by linarith
  change inner ℝ h (J h + γ • projectedGram R h s) = 0
  rw [inner_add_right, real_inner_smul_right, hrev,
    projectedGram_energy_pairing, mul_zero, add_zero]

/-- The full entropy rate has the Gram readout when the reversible map kills s. -/
theorem projectedGramFlow_entropy_rate (R : ι → E →L[ℝ] F) (h s : E)
    (J : E →L[ℝ] E) (hJ : J.adjoint = -J) (hJs : J s = 0)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    inner ℝ s (projectedGramFlow R h s J γ hγ).totalFlow =
      γ * ∑ i, ‖R i ((ℝ ∙ h)ᗮ.starProjection s)‖ ^ 2 := by
  have hrev : inner ℝ s (J h) = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left J h s, hJ,
      neg_apply, hJs, neg_zero, inner_zero_left]
  change inner ℝ s (J h + γ • projectedGram R h s) = _
  rw [inner_add_right, hrev, zero_add, real_inner_smul_right, projectedGram_quadratic]

theorem projectedGramFlow_entropy_rate_nonneg (R : ι → E →L[ℝ] F) (h s : E)
    (J : E →L[ℝ] E) (hJ : J.adjoint = -J) (hJs : J s = 0)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ inner ℝ s (projectedGramFlow R h s J γ hγ).totalFlow := by
  rw [projectedGramFlow_entropy_rate R h s J hJ hJs]
  exact mul_nonneg hγ (Finset.sum_nonneg fun i _ => sq_nonneg _)

end InfoGeometry.Thermo.ProjectedGramDissipation
