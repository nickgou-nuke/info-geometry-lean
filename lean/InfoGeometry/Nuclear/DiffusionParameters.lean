/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Nuclear.RadonDiffusionProfiles
import Mathlib.Analysis.Real.Sqrt

/-!
# Storage, apparent diffusivity, and dimensionless attenuation

The bulk flux coefficient `B` and storage factor `S` give apparent diffusivity
`B / S`. The residual equivalence retains the regularity requirements of the
profile owner's `SolvesDiffusionDecay`. Parameter reconstruction is conditional
on the stated equations; no fitted value or experimental inference is assumed.

The zero-loss Dirichlet baseline is linear and the zero-loss Neumann baseline
is constant. These are proved directly, without substituting zero attenuation
into the singular sinh normalization or asserting a parameter limit.
Normalized attenuation is the actual ratio to the same-inlet linear baseline.
-/

noncomputable section

namespace InfoGeometry.Nuclear.DiffusionParameters

open InfoGeometry.Nuclear.RadonDiffusionProfiles

/-- Factor the storage-form residual without identifying bulk and pore diffusivity. -/
theorem storage_residual_factor (B S lambda C C₂ : ℝ) (hS : S ≠ 0) :
    B * C₂ - lambda * S * C = S * ((B / S) * C₂ - lambda * C) := by
  field_simp [hS]

theorem storage_residual_zero_iff (B S lambda C C₂ : ℝ) (hS : S ≠ 0) :
    B * C₂ - lambda * S * C = 0 ↔ (B / S) * C₂ - lambda * C = 0 := by
  rw [storage_residual_factor B S lambda C C₂ hS]
  simp only [mul_eq_zero, hS, false_or]

/-- The equation rewrite preserves both actual differentiability hypotheses. -/
theorem solves_apparent_iff_storage (B S lambda : ℝ) (C : ℝ → ℝ) (hS : S ≠ 0) :
    SolvesDiffusionDecay (B / S) lambda C ↔
      Differentiable ℝ C ∧ Differentiable ℝ (deriv C) ∧
        ∀ x, B * deriv (deriv C) x - lambda * S * C x = 0 := by
  constructor
  · rintro ⟨hC, hC₂, h⟩
    refine ⟨hC, hC₂, fun x => ?_⟩
    exact (storage_residual_zero_iff B S lambda (C x) (deriv (deriv C) x) hS).mpr (h x)
  · rintro ⟨hC, hC₂, h⟩
    refine ⟨hC, hC₂, fun x => ?_⟩
    exact (storage_residual_zero_iff B S lambda (C x) (deriv (deriv C) x) hS).mp (h x)

/-- The nonnegative square root gives the required attenuation relation. -/
theorem sqrt_attenuation_relation (D lambda : ℝ) (hD : 0 < D) (hlambda : 0 ≤ lambda) :
    D * (Real.sqrt (lambda / D)) ^ 2 = lambda := by
  rw [Real.sq_sqrt (div_nonneg hlambda hD.le)]
  field_simp [ne_of_gt hD]

/-- Multiplying inverse length by cell width yields the dimensionless relation. -/
theorem cell_attenuation_relation (D lambda k d : ℝ) (hrel : D * k ^ 2 = lambda) :
    D * (k * d) ^ 2 = lambda * d ^ 2 := by
  rw [mul_pow, ← mul_assoc, hrel]

/-- Recover apparent diffusivity from the dimensionless cell attenuation relation. -/
theorem diffusivity_from_cell_attenuation (D lambda d mu : ℝ) (hmu : mu ≠ 0)
    (hrel : D * mu ^ 2 = lambda * d ^ 2) :
    D = lambda * (d / mu) ^ 2 := by
  rw [div_pow, ← mul_div_assoc]
  exact (eq_div_iff (pow_ne_zero 2 hmu)).mpr hrel

/-- No-loss Dirichlet profile with inlet `C0` and outlet zero when `L ≠ 0`. -/
def linearDirichlet (C0 L x : ℝ) : ℝ := C0 * (L - x) / L

/-- No-loss Neumann profile with fixed inlet and zero spatial derivative. -/
def constantNeumann (C0 : ℝ) (_x : ℝ) : ℝ := C0

theorem hasDerivAt_linearDirichlet (C0 L x : ℝ) :
    HasDerivAt (linearDirichlet C0 L) (-C0 / L) x := by
  unfold linearDirichlet
  convert (((hasDerivAt_id' x).const_sub L).const_mul C0).div_const L using 1 <;> ring

theorem deriv_linearDirichlet (C0 L : ℝ) :
    deriv (linearDirichlet C0 L) = fun _ => -C0 / L := by
  funext x
  exact (hasDerivAt_linearDirichlet C0 L x).deriv

theorem linearDirichlet_inlet (C0 L : ℝ) (hL : L ≠ 0) :
    linearDirichlet C0 L 0 = C0 := by simp [linearDirichlet, hL]

@[simp] theorem linearDirichlet_outlet (C0 L : ℝ) :
    linearDirichlet C0 L L = 0 := by simp [linearDirichlet]

theorem linearDirichlet_solves (C0 L D : ℝ) :
    SolvesDiffusionDecay D 0 (linearDirichlet C0 L) := by
  refine ⟨fun x => (hasDerivAt_linearDirichlet C0 L x).differentiableAt, ?_, ?_⟩
  · rw [deriv_linearDirichlet]
    exact differentiable_const _
  · intro x
    rw [deriv_linearDirichlet]
    simp [deriv_const]

@[simp] theorem constantNeumann_inlet (C0 : ℝ) : constantNeumann C0 0 = C0 := rfl

theorem constantNeumann_outlet_derivative (C0 L : ℝ) :
    deriv (constantNeumann C0) L = 0 := by
  unfold constantNeumann
  exact deriv_const L C0

theorem constantNeumann_solves (C0 D : ℝ) :
    SolvesDiffusionDecay D 0 (constantNeumann C0) := by
  have hderiv : deriv (constantNeumann C0) = (fun _ : ℝ => (0 : ℝ)) := by
    funext x
    exact constantNeumann_outlet_derivative C0 x
  refine ⟨differentiable_const C0, ?_, ?_⟩
  · rw [hderiv]
    exact differentiable_const (0 : ℝ)
  · intro x
    rw [hderiv]
    simp only [deriv_const, mul_zero, zero_mul, sub_self]

/-- Dimensionless attenuation relative to the same-inlet, zero-loss profile. -/
def normalizedDirichlet (C0 k L x : ℝ) : ℝ :=
  dirichletProfile C0 k L x / linearDirichlet C0 L x

/-- Normalization cancels the inlet amplitude and retains the physical geometry. -/
theorem normalizedDirichlet_formula (C0 k L x : ℝ)
    (hC0 : C0 ≠ 0) (hL : L ≠ 0) (hx : L - x ≠ 0)
    (hs : Real.sinh (k * L) ≠ 0) :
    normalizedDirichlet C0 k L x =
      (L / (L - x)) * Real.sinh (k * (L - x)) / Real.sinh (k * L) := by
  unfold normalizedDirichlet dirichletProfile sinhProfile linearDirichlet
  field_simp [hC0, hL, hx, hs]

end InfoGeometry.Nuclear.DiffusionParameters
