/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.OperatorDirichletLaplacian
import Mathlib.Tactic.Linarith

/-!
# Energy-constrained Dirichlet mobility

For a finite family of bounded maps `Tᵢ` on a complex Hilbert space and an
energy direction `h`, project onto the actual orthogonal complement of `ℂ h`
and construct `M = P (∑ᵢ Tᵢ† Tᵢ) P`. Positivity and the energy kernel are
consequences of this construction. The projected maps need not commute.

The final rates concern the vector `J h + M s` at one state. Interpreting
`h` and `s` as gradients and this vector as a physical evolution requires
those additional definitions. No density preservation or reservoir law is
asserted here.
-/

noncomputable section

open scoped BigOperators InnerProductSpace
open ContinuousLinearMap

namespace InfoGeometry.Analysis.ConstrainedDirichletLaplacian

open InfoGeometry.Analysis.OperatorDirichletLaplacian

variable {ι E F : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The actual orthogonal projection onto the complement of the energy
direction. This definition also covers `h = 0`. -/
def energyProjection (h : E) : E →L[ℂ] E :=
  (ℂ ∙ h)ᗮ.starProjection

theorem energyProjection_adjoint (h : E) :
    adjoint (energyProjection h) = energyProjection h :=
  (ℂ ∙ h)ᗮ.starProjection_isSymmetric.clm_adjoint_eq

omit [CompleteSpace E] in
@[simp] theorem energyProjection_self (h : E) :
    energyProjection h h = 0 :=
  Submodule.starProjection_orthogonalComplement_singleton_eq_zero h

omit [CompleteSpace E] in
/-- The removed component is the energy direction itself; no nonzero
hypothesis is needed because Mathlib treats zero projection correctly. -/
theorem energyProjection_apply (h x : E) :
    energyProjection h x =
      x - (inner ℂ h x / ((‖h‖ ^ 2 : ℝ) : ℂ)) • h := by
  rw [energyProjection, Submodule.starProjection_orthogonal']
  change x - (ℂ ∙ h).starProjection x = _
  rw [Submodule.starProjection_singleton]
  rfl

/-- Compress the existing Dirichlet family before taking its sum of squares. -/
def constrainedLaplacian (T : ι → E →L[ℂ] F) (h : E) : E →L[ℂ] E :=
  laplacian (fun i => (T i).comp (energyProjection h))

/-- Compression is an equality of bounded operators, not only of quadratic forms. -/
theorem constrainedLaplacian_eq_compression (T : ι → E →L[ℂ] F) (h : E) :
    constrainedLaplacian T h =
      (energyProjection h).comp ((laplacian T).comp (energyProjection h)) := by
  rw [constrainedLaplacian, laplacian_precompose, energyProjection_adjoint]

theorem constrainedLaplacian_isPositive (T : ι → E →L[ℂ] F) (h : E) :
    (constrainedLaplacian T h).IsPositive :=
  isPositive_laplacian _

theorem constrainedLaplacian_isSelfAdjoint (T : ι → E →L[ℂ] F) (h : E) :
    IsSelfAdjoint (constrainedLaplacian T h) :=
  isSelfAdjoint_laplacian _

/-- The energy direction is a proved zero mode of the compressed mobility. -/
@[simp] theorem constrainedLaplacian_energy (T : ι → E →L[ℂ] F) (h : E) :
    constrainedLaplacian T h h = 0 := by
  apply (laplacian_apply_eq_zero_iff _ _).mpr
  intro i
  simp only [comp_apply, energyProjection_self, map_zero]

/-- Every dissipative output is orthogonal to the energy direction. -/
theorem inner_energy_constrainedLaplacian
    (T : ι → E →L[ℂ] F) (h x : E) :
    inner ℂ h (constrainedLaplacian T h x) = 0 := by
  rw [constrainedLaplacian_eq_compression]
  simp only [comp_apply]
  rw [← energyProjection_adjoint h, adjoint_inner_right,
    energyProjection_self, inner_zero_left]

/-- The quadratic form measures the original maps on the projected direction. -/
theorem re_inner_constrainedLaplacian
    (T : ι → E →L[ℂ] F) (h x : E) :
    (inner ℂ x (constrainedLaplacian T h x)).re =
      ∑ i, ‖T i (energyProjection h x)‖ ^ 2 :=
  re_inner_laplacian _ _

theorem re_inner_constrainedLaplacian_nonneg
    (T : ι → E →L[ℂ] F) (h x : E) :
    0 ≤ (inner ℂ x (constrainedLaplacian T h x)).re := by
  rw [re_inner_constrainedLaplacian]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Compression changes the kernel by testing the projected argument. -/
theorem constrainedLaplacian_apply_eq_zero_iff
    (T : ι → E →L[ℂ] F) (h x : E) :
    constrainedLaplacian T h x = 0 ↔
      ∀ i, T i (energyProjection h x) = 0 :=
  laplacian_apply_eq_zero_iff _ _

theorem re_inner_constrainedLaplacian_eq_zero_iff
    (T : ι → E →L[ℂ] F) (h x : E) :
    (inner ℂ x (constrainedLaplacian T h x)).re = 0 ↔
      ∀ i, T i (energyProjection h x) = 0 := by
  rw [re_inner_constrainedLaplacian]
  exact energy_eq_zero_iff T (energyProjection h x)

/-- Zero production is equivalent to zero dissipative motion. -/
theorem re_inner_constrainedLaplacian_eq_zero_iff_apply_eq_zero
    (T : ι → E →L[ℂ] F) (h x : E) :
    (inner ℂ x (constrainedLaplacian T h x)).re = 0 ↔
      constrainedLaplacian T h x = 0 := by
  rw [re_inner_constrainedLaplacian_eq_zero_iff,
    constrainedLaplacian_apply_eq_zero_iff]

theorem re_inner_constrainedLaplacian_pos_iff
    (T : ι → E →L[ℂ] F) (h x : E) :
    0 < (inner ℂ x (constrainedLaplacian T h x)).re ↔
      ∃ i, T i (energyProjection h x) ≠ 0 := by
  rw [re_inner_constrainedLaplacian]
  exact energy_pos_iff T (energyProjection h x)

/-- A skew-adjoint reversible map has zero real self-pairing. -/
theorem re_inner_skewAdjoint_apply (J : E →L[ℂ] E)
    (hJ : adjoint J = -J) (x : E) :
    (inner ℂ x (J x)).re = 0 := by
  have hp := congrArg Complex.re (adjoint_inner_right J x x)
  rw [hJ, neg_apply, inner_neg_right, Complex.neg_re] at hp
  have hs : (inner ℂ (J x) x).re = (inner ℂ x (J x)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  linarith only [hp, hs]

/-- The entropy Casimir condition eliminates the reversible entropy rate. -/
theorem inner_skewAdjoint_apply_eq_zero (J : E →L[ℂ] E)
    (hJ : adjoint J = -J) (h s : E) (hs : J s = 0) :
    inner ℂ s (J h) = 0 := by
  have hp := adjoint_inner_right J s h
  rw [hJ, neg_apply, inner_neg_right, hs, inner_zero_left] at hp
  exact neg_eq_zero.mp hp

/-- First-law rate for the constructed dissipative operator and an explicit
skew-adjoint reversible operator. -/
theorem generic_energy_rate (T : ι → E →L[ℂ] F) (h s : E)
    (J : E →L[ℂ] E) (hJ : adjoint J = -J) :
    (inner ℂ h (J h + constrainedLaplacian T h s)).re = 0 := by
  rw [inner_add_right, Complex.add_re,
    re_inner_skewAdjoint_apply J hJ,
    inner_energy_constrainedLaplacian, Complex.zero_re, add_zero]

/-- Exact pointwise second-law rate: the entropy Casimir hypothesis is
explicit, while positivity comes from the compressed sum-of-squares construction. -/
theorem generic_entropy_rate (T : ι → E →L[ℂ] F) (h s : E)
    (J : E →L[ℂ] E) (hJ : adjoint J = -J) (hs : J s = 0) :
    (inner ℂ s (J h + constrainedLaplacian T h s)).re =
      ∑ i, ‖T i (energyProjection h s)‖ ^ 2 := by
  rw [inner_add_right, inner_skewAdjoint_apply_eq_zero J hJ h s hs,
    zero_add, re_inner_constrainedLaplacian]

theorem generic_entropy_rate_nonneg (T : ι → E →L[ℂ] F) (h s : E)
    (J : E →L[ℂ] E) (hJ : adjoint J = -J) (hs : J s = 0) :
    0 ≤ (inner ℂ s (J h + constrainedLaplacian T h s)).re := by
  rw [generic_entropy_rate T h s J hJ hs]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The complete vector may still have reversible motion when entropy
production vanishes; the dissipative summand vanishes exactly. -/
theorem generic_entropy_rate_eq_zero_iff (T : ι → E →L[ℂ] F) (h s : E)
    (J : E →L[ℂ] E) (hJ : adjoint J = -J) (hs : J s = 0) :
    (inner ℂ s (J h + constrainedLaplacian T h s)).re = 0 ↔
      constrainedLaplacian T h s = 0 := by
  rw [generic_entropy_rate T h s J hJ hs,
    constrainedLaplacian_apply_eq_zero_iff]
  exact energy_eq_zero_iff T (energyProjection h s)

end InfoGeometry.Analysis.ConstrainedDirichletLaplacian
