/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Tactic

/-!
# Algebraic Foldy–Wouthuysen / Plabic loop-coordinate identities

This file formalizes the real, subcritical scalar reparameterization appearing
in the shared Gemini transcript. It proves the rational loop prefactor and
dressed strand coordinates from a rapidity parameter. It does not identify an
analytic differential form, prove a complex urban-renewal continuation, or
derive a physical mass interpretation.
-/

namespace InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge

/-- The loop parameter corresponding to the squared hyperbolic velocity. -/
noncomputable def loopWeight (θ : ℝ) : ℝ := -(Real.tanh θ) ^ 2

/-- The two directed strand weights with opposite chiral rapidity factors. -/
noncomputable def lowerStrand (θ χ : ℝ) : ℝ := Real.tanh θ * Real.exp (-χ)
noncomputable def upperStrand (θ χ : ℝ) : ℝ := Real.tanh θ * Real.exp χ

/-- The common Schur denominator is strictly positive at every finite real
rapidity, so the real parameterization stays away from the pole `f = -1`. -/
theorem schurDenominator_pos (θ : ℝ) : 0 < 1 + loopWeight θ := by
  dsimp [loopWeight]
  have h := Real.tanh_sq_lt_one θ
  nlinarith

/-- Every negative loop weight strictly above the Schur pole has a real
rapidity representative.  The inverse is selected canonically by requiring
`θ ≥ 0`, via `artanh (sqrt (-f))`. -/
theorem loopWeight_artanh_sqrt (f : ℝ) (hf₀ : -1 < f) (hf₁ : f < 0) :
    loopWeight (Real.artanh (Real.sqrt (-f))) = f := by
  have hnonneg : 0 ≤ -f := by linarith
  have hlt : Real.sqrt (-f) < 1 := by
    have hsqrt := Real.sq_sqrt hnonneg
    nlinarith [Real.sqrt_nonneg (-f)]
  have htanh : Real.tanh (Real.artanh (Real.sqrt (-f))) = Real.sqrt (-f) :=
    Real.tanh_artanh (Set.mem_Ioo.mpr
      ⟨by nlinarith [Real.sqrt_nonneg (-f)], hlt⟩)
  dsimp [loopWeight]
  rw [htanh, Real.sq_sqrt hnonneg]
  ring

/-- The Schur denominator is the squared hyperbolic secant. -/
theorem schurDenominator_eq_inv_cosh_sq (θ : ℝ) :
    1 + loopWeight θ = (Real.cosh θ)⁻¹ ^ 2 := by
  dsimp [loopWeight]
  have hc : Real.cosh θ ≠ 0 := (Real.cosh_pos θ).ne'
  calc 1 - (Real.tanh θ) ^ 2
      = 1 - (Real.sinh θ / Real.cosh θ) ^ 2 := by
          rw [Real.tanh_eq_sinh_div_cosh]
    _ = ((Real.cosh θ) ^ 2 - (Real.sinh θ) ^ 2) / (Real.cosh θ) ^ 2 := by
          field_simp
    _ = 1 / (Real.cosh θ) ^ 2 := by rw [Real.cosh_sq_sub_sinh_sq]
    _ = (Real.cosh θ)⁻¹ ^ 2 := by ring

/-- The rational Plabic prefactor becomes the Lorentz factor `cosh(2θ)`. -/
theorem loopPrefactor_eq_cosh_two (θ : ℝ) :
    (1 - loopWeight θ) / (1 + loopWeight θ) = Real.cosh (2 * θ) := by
  dsimp [loopWeight]
  have hc : Real.cosh θ ≠ 0 := (Real.cosh_pos θ).ne'
  calc (1 - -((Real.tanh θ) ^ 2)) / (1 + -((Real.tanh θ) ^ 2))
      = (1 + (Real.tanh θ) ^ 2) / (1 - (Real.tanh θ) ^ 2) := by ring
    _ = ((Real.cosh θ) ^ 2 + (Real.sinh θ) ^ 2) /
          ((Real.cosh θ) ^ 2 - (Real.sinh θ) ^ 2) := by
            rw [Real.tanh_eq_sinh_div_cosh]
            field_simp
    _ = (Real.cosh θ) ^ 2 + (Real.sinh θ) ^ 2 := by
          rw [Real.cosh_sq_sub_sinh_sq]
          ring
    _ = Real.cosh (2 * θ) := by rw [Real.cosh_two_mul]

/-- The common dressed radial coefficient is `sinh(2θ)/2`. -/
theorem tanh_over_schurDenominator_eq_half_sinh_two (θ : ℝ) :
    Real.tanh θ / (1 - (Real.tanh θ) ^ 2) =
      (1 / 2 : ℝ) * Real.sinh (2 * θ) := by
  have hc : Real.cosh θ ≠ 0 := (Real.cosh_pos θ).ne'
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul]
  have hden : 1 - (Real.sinh θ / Real.cosh θ) ^ 2 =
      1 / (Real.cosh θ) ^ 2 := by
    calc 1 - (Real.sinh θ / Real.cosh θ) ^ 2
        = ((Real.cosh θ) ^ 2 - (Real.sinh θ) ^ 2) / (Real.cosh θ) ^ 2 := by
            field_simp
      _ = 1 / (Real.cosh θ) ^ 2 := by rw [Real.cosh_sq_sub_sinh_sq]
  rw [hden]
  field_simp

/-- Pullback of the lower directed strand after division by the Schur
denominator. -/
theorem lowerDressedStrand_eq (θ χ : ℝ) :
    lowerStrand θ χ / (1 + loopWeight θ) =
      (1 / 2 : ℝ) * Real.sinh (2 * θ) * Real.exp (-χ) := by
  dsimp [lowerStrand, loopWeight]
  have hd : 1 - (Real.tanh θ) ^ 2 ≠ 0 :=
    (sub_pos.mpr (by nlinarith [Real.tanh_sq_lt_one θ])).ne'
  calc (Real.tanh θ * Real.exp (-χ)) / (1 - (Real.tanh θ) ^ 2)
      = (Real.tanh θ / (1 - (Real.tanh θ) ^ 2)) * Real.exp (-χ) := by
          field_simp
    _ = ((1 / 2 : ℝ) * Real.sinh (2 * θ)) * Real.exp (-χ) := by
          rw [tanh_over_schurDenominator_eq_half_sinh_two]

/-- Pullback of the upper directed strand after division by the Schur
denominator. -/
theorem upperDressedStrand_eq (θ χ : ℝ) :
    upperStrand θ χ / (1 + loopWeight θ) =
      (1 / 2 : ℝ) * Real.sinh (2 * θ) * Real.exp χ := by
  dsimp [upperStrand, loopWeight]
  have hd : 1 - (Real.tanh θ) ^ 2 ≠ 0 :=
    (sub_pos.mpr (by nlinarith [Real.tanh_sq_lt_one θ])).ne'
  calc (Real.tanh θ * Real.exp χ) / (1 - (Real.tanh θ) ^ 2)
      = (Real.tanh θ / (1 - (Real.tanh θ) ^ 2)) * Real.exp χ := by
          field_simp
    _ = ((1 / 2 : ℝ) * Real.sinh (2 * θ)) * Real.exp χ := by
          rw [tanh_over_schurDenominator_eq_half_sinh_two]

/-- The two dressed channels have rapidity-independent product. -/
theorem dressedStrand_product (θ χ : ℝ) :
    (lowerStrand θ χ / (1 + loopWeight θ)) *
      (upperStrand θ χ / (1 + loopWeight θ)) =
        ((Real.sinh (2 * θ)) ^ 2) / 4 := by
  rw [lowerDressedStrand_eq, upperDressedStrand_eq]
  have hexp : Real.exp (-χ) * Real.exp χ = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc ((1 / 2 : ℝ) * Real.sinh (2 * θ) * Real.exp (-χ)) *
        ((1 / 2 : ℝ) * Real.sinh (2 * θ) * Real.exp χ)
      = (((1 / 2 : ℝ) * (1 / 2 : ℝ)) *
          (Real.sinh (2 * θ)) ^ 2) * (Real.exp (-χ) * Real.exp χ) := by ring
    _ = ((1 / 2 : ℝ) * (1 / 2 : ℝ)) * (Real.sinh (2 * θ)) ^ 2 := by
          rw [hexp, mul_one]
    _ = (Real.sinh (2 * θ)) ^ 2 / 4 := by ring

end InfoGeometry.Physics.FoldyWouthuysenPlabicRapidityBridge
