import Mathlib.NumberTheory.LSeries.RiemannZeta
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-!
# Native zeta functional-equation layer

This module contains functions, predicates, and proved theorems.  It does not
encode functional equations, theta modularity, Dirac self-adjointness, or
zero-location conclusions as fields of evidence structures.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZetaFunctionalEquationLayer

open Complex
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-! ## Prime holonomy -/

/-- Prime holonomy `p^(1/2-s)`. -/
@[rep_depth operator]
def primeHolonomy (p : ℕ) (s : ℂ) : ℂ :=
  (p : ℂ) ^ ((1 / 2 : ℂ) - s)

/-- Riemann reflection `s ↦ 1-s`. -/
@[rep_depth operator]
def riemannReflection (s : ℂ) : ℂ :=
  1 - s

@[rep_depth operator]
theorem riemannReflection_involutive :
    Function.Involutive riemannReflection := by
  intro s
  unfold riemannReflection
  ring

@[rep_depth operator]
theorem riemannReflection_preserves_criticalLine
    (s : ℂ)
    (hs : OnCriticalLine s) :
    OnCriticalLine (riemannReflection s) := by
  unfold OnCriticalLine riemannReflection at *
  simp [hs]
  linarith

@[rep_depth operator]
theorem reflection_exponent_neg (s : ℂ) :
    (1 / 2 : ℂ) - riemannReflection s =
      -((1 / 2 : ℂ) - s) := by
  unfold riemannReflection
  ring

@[rep_depth operator]
theorem primeHolonomy_reflection_eq_inv
    (p : ℕ)
    (s : ℂ) :
    primeHolonomy p (riemannReflection s) =
      (primeHolonomy p s)⁻¹ := by
  unfold primeHolonomy
  rw [reflection_exponent_neg]
  exact cpow_neg (p : ℂ) ((1 / 2 : ℂ) - s)

@[rep_depth operator]
theorem holonomy_exponent_pure_imaginary
    (s : ℂ)
    (hs : OnCriticalLine s) :
    ((1 / 2 : ℂ) - s).re = 0 := by
  unfold OnCriticalLine at hs
  simp [Complex.sub_re]
  linarith

@[rep_depth operator]
theorem primeHolonomy_norm_one_of_criticalLine
    (p : ℕ)
    (hp : 1 < p)
    (s : ℂ)
    (hs : OnCriticalLine s) :
    ‖primeHolonomy p s‖ = 1 := by
  unfold primeHolonomy
  have hpos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hcast : (p : ℂ) = ((p : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, norm_cpow_eq_rpow_re_of_pos hpos,
    holonomy_exponent_pure_imaginary s hs, Real.rpow_zero]

/-- Inversion is conjugation on the complex unit circle. -/
@[rep_depth operator]
theorem inv_eq_conj_of_norm_one
    (z : ℂ)
    (hz : ‖z‖ = 1) :
    z⁻¹ = starRingEnd ℂ z := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
  norm_num

@[rep_depth operator]
theorem primeHolonomy_inv_eq_conj_of_criticalLine
    (p : ℕ)
    (hp : 1 < p)
    (s : ℂ)
    (hs : OnCriticalLine s) :
    (primeHolonomy p s)⁻¹ =
      starRingEnd ℂ (primeHolonomy p s) :=
  inv_eq_conj_of_norm_one _
    (primeHolonomy_norm_one_of_criticalLine p hp s hs)

/-! The compatibility packet below contains only the two native theorem
owners above.  It does not introduce an additional analytic assumption. -/

@[rep_depth operator]
structure HolonomyInversionIsConjugation where
  inv_eq_conj_of_norm_one :
    ∀ (z : ℂ), ‖z‖ = 1 → z⁻¹ = starRingEnd ℂ z
  holonomy_inv_eq_conj :
    ∀ (p : ℕ), 1 < p → ∀ (s : ℂ), OnCriticalLine s →
      (primeHolonomy p s)⁻¹ = starRingEnd ℂ (primeHolonomy p s)

@[rep_depth operator]
def nativeHolonomyInversionIsConjugation :
    HolonomyInversionIsConjugation where
  inv_eq_conj_of_norm_one := inv_eq_conj_of_norm_one
  holonomy_inv_eq_conj := primeHolonomy_inv_eq_conj_of_criticalLine

/-! ## Completed xi -/

/-- Pole-removed completed Riemann xi function. -/
@[rep_depth operator]
def completedRiemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s

@[rep_depth operator]
theorem completedRiemannXi_reflection (s : ℂ) :
    completedRiemannXi s =
      completedRiemannXi (riemannReflection s) := by
  unfold completedRiemannXi riemannReflection
  rw [completedRiemannZeta_one_sub]
  ring

/-! ## Cayley compactification -/

@[rep_depth operator]
theorem cayley_reflection_eq_inversion (s : ℂ) :
    cayleyToFugacity (riemannReflection s) =
      (cayleyToFugacity s)⁻¹ := by
  unfold riemannReflection
  exact cayleyToFugacity_one_sub_eq_inv s

/-- Completed xi in the Cayley coordinate. -/
@[rep_depth operator]
def cayleyCompletedXi (w : ℂ) : ℂ :=
  completedRiemannXi (1 / (1 - w))

/-- Inverting the Cayley coordinate reflects the Riemann coordinate. -/
@[rep_depth operator]
theorem cayleyParameter_inv_eq_reflection
    {w : ℂ}
    (hw : w ≠ 0)
    (h1w : 1 - w ≠ 0) :
    1 / (1 - w⁻¹) = riemannReflection (1 / (1 - w)) := by
  unfold riemannReflection
  have hw1 : w ≠ 1 := by
    intro h
    apply h1w
    rw [h]
    norm_num
  have hwm1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  calc
    1 / (1 - w⁻¹) = w / (w - 1) := by
      field_simp [hw, hwm1]
    _ = -w / (1 - w) := by
      field_simp [h1w, hwm1]
      ring
    _ = 1 - 1 / (1 - w) := by
      field_simp [h1w]
      ring

/-- The Cayley-completed xi function is invariant under inversion. -/
@[rep_depth operator]
theorem cayleyCompletedXi_inversion
    {w : ℂ}
    (hw : w ≠ 0)
    (h1w : 1 - w ≠ 0) :
    cayleyCompletedXi w = cayleyCompletedXi w⁻¹ := by
  unfold cayleyCompletedXi
  rw [cayleyParameter_inv_eq_reflection hw h1w]
  exact completedRiemannXi_reflection _

/-! ## Disk inversion -/

/-- Complex inversion exchanges the interior and exterior of the unit disk. -/
@[rep_depth operator]
theorem norm_lt_one_iff_norm_inv_gt_one
    {w : ℂ}
    (hw : w ≠ 0) :
    ‖w‖ < 1 ↔ 1 < ‖w⁻¹‖ := by
  rw [norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hw)).symm

/-- Complex inversion exchanges the exterior and interior of the unit disk. -/
@[rep_depth operator]
theorem norm_gt_one_iff_norm_inv_lt_one
    {w : ℂ}
    (hw : w ≠ 0) :
    1 < ‖w‖ ↔ ‖w⁻¹‖ < 1 := by
  rw [norm_inv]
  exact (inv_lt_one₀ (norm_pos_iff.mpr hw)).symm

/-! ## Honest open theorem statements -/

/-- Jacobi theta modularity, stated for a concrete candidate function. -/
def IsThetaModular (theta : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x →
    theta x = x ^ (-(1 / 2 : ℝ)) * theta (1 / x)

/--
The exact self-adjointness/critical-line theorem required of a concrete Dirac
family.  No Dirac object is manufactured by this definition.
-/
def DiracSelfAdjointExactlyOnCriticalLine
    (isSelfAdjoint : ℂ → Prop) : Prop :=
  ∀ s : ℂ, isSelfAdjoint s ↔ OnCriticalLine s

/--
The Cayley zero-location target for completed xi.  Constructing a proof of
this proposition is equivalent to the corresponding RH zero-location result;
the definition supplies no evidence.
-/
def CayleyCompletedXiZerosOnUnitCircle : Prop :=
  ∀ w : ℂ,
    w ≠ 0 →
    1 - w ≠ 0 →
    cayleyCompletedXi w = 0 →
    ‖w‖ = 1

end InfoGeometry.Canonical.ZetaFunctionalEquationLayer
