/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.FixedGroundHamiltonianFiber
import InfoGeometry.Analysis.RealPositiveOperatorGap
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Uniform spectral gap along a fixed-ground-space interpolation

In finite dimension the quadratic lower bound defining the fixed-ground
Hamiltonian fiber gives a gap for the spectrum of the actual continuous
operator. This uses the existing positive-operator gap owner and Mathlib's
equality of continuous and algebraic operator spectra. The same fixed gap
persists along every convex interpolation inside the fiber.
-/

namespace InfoGeometry.Analysis.FixedGroundHamiltonianSpectrum

open FixedGroundHamiltonianFiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A member of the fiber has no nonzero real spectral value below the fixed
positive quadratic lower bound. -/
theorem spectrum_gap_of_mem (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ) {H : E →L[ℝ] E}
    (hH : H ∈ fixedGroundFiber K δ) {μ : ℝ} (hμ : μ ∈ spectrum ℝ H) :
    μ = 0 ∨ δ ≤ μ := by
  have hbound : ∀ x ∈ H.toLinearMap.kerᗮ, δ * ‖x‖ ^ 2 ≤ inner ℝ x (H x) := by
    intro x hx
    apply lower_bound_on_orthogonal K δ hH
    simpa only [ker_eq_of_mem K δ hH hδ] using hx
  exact RealPositiveOperatorGap.spectrum_gap_of_coercive_bound H.toLinearMap hH.1 hbound
    (by simpa only [ContinuousLinearMap.spectrum_eq] using hμ)

/-- Convex interpolation preserves the same positive gap in the actual
operator spectrum, with no commutation condition on its endpoints. -/
theorem interpolation_spectrum_gap (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    {δ : ℝ} (hδ : 0 < δ) {H₀ H₁ : E →L[ℝ] E}
    (h₀ : H₀ ∈ fixedGroundFiber K δ) (h₁ : H₁ ∈ fixedGroundFiber K δ)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ ((1 - t) • H₀ + t • H₁)) : μ = 0 ∨ δ ≤ μ :=
  spectrum_gap_of_mem K hδ (interpolation_mem K δ h₀ h₁ ht₀ ht₁) hμ

end InfoGeometry.Analysis.FixedGroundHamiltonianSpectrum
