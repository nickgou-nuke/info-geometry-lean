/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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

/-- The rapidity coordinate has the standard hyperbolic derivative. This
is the analytic input needed to interpret the loop-coordinate identities as
a Jacobian pullback. -/
theorem hasDerivAt_tanh (θ : ℝ) :
    HasDerivAt Real.tanh ((Real.cosh θ)⁻¹ ^ 2) θ := by
  have hc : Real.cosh θ ≠ 0 := (Real.cosh_pos θ).ne'
  have hdiv := (Real.hasDerivAt_sinh θ).div (Real.hasDerivAt_cosh θ) hc
  have hquot : HasDerivAt Real.tanh
      ((Real.cosh θ * Real.cosh θ - Real.sinh θ * Real.sinh θ) /
        (Real.cosh θ) ^ 2) θ := by
    convert hdiv using 1
    funext x
    exact Real.tanh_eq_sinh_div_cosh x
  have hcoeff :
      (Real.cosh θ * Real.cosh θ - Real.sinh θ * Real.sinh θ) /
          (Real.cosh θ) ^ 2 = (Real.cosh θ)⁻¹ ^ 2 := by
    field_simp [hc]
    rw [Real.cosh_sq_sub_sinh_sq]
  exact hquot.congr_deriv hcoeff

/-- The derivative of `tanh` in the reciprocal-cosh-square form. -/
theorem deriv_tanh_eq_inv_cosh_sq (θ : ℝ) :
    deriv Real.tanh θ = (Real.cosh θ)⁻¹ ^ 2 :=
  (hasDerivAt_tanh θ).deriv

/-- Logarithmic rapidity coordinates of the two bare directed strands. -/
noncomputable def lowerLogCoordinate (θ χ : ℝ) : ℝ := Real.log (Real.tanh θ) - χ
noncomputable def upperLogCoordinate (θ χ : ℝ) : ℝ := Real.log (Real.tanh θ) + χ

private theorem tanh_pos_of_pos {θ : ℝ} (hθ : 0 < θ) : 0 < Real.tanh θ := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hθ) (Real.cosh_pos θ)

/-- On the positive rapidity corridor, the logarithm of the lower bare strand
is its logarithmic rapidity coordinate. -/
theorem log_lowerStrand_eq (θ χ : ℝ) (hθ : 0 < θ) :
    Real.log (lowerStrand θ χ) = lowerLogCoordinate θ χ := by
  dsimp [lowerStrand, lowerLogCoordinate]
  rw [Real.log_mul (ne_of_gt (tanh_pos_of_pos hθ)) (Real.exp_ne_zero _),
    Real.log_exp]
  ring

/-- The matching logarithmic identity for the upper directed strand. -/
theorem log_upperStrand_eq (θ χ : ℝ) (hθ : 0 < θ) :
    Real.log (upperStrand θ χ) = upperLogCoordinate θ χ := by
  dsimp [upperStrand, upperLogCoordinate]
  rw [Real.log_mul (ne_of_gt (tanh_pos_of_pos hθ)) (Real.exp_ne_zero _),
    Real.log_exp]

/-- The rapidity derivative of either bare logarithmic strand. -/
theorem hasDerivAt_log_tanh (θ : ℝ) (hθ : 0 < θ) :
    HasDerivAt (fun t : ℝ => Real.log (Real.tanh t))
      (1 / (Real.sinh θ * Real.cosh θ)) θ := by
  have ht : 0 < Real.tanh θ := tanh_pos_of_pos hθ
  have hs : 0 < Real.sinh θ := Real.sinh_pos_iff.mpr hθ
  have hc : 0 < Real.cosh θ := Real.cosh_pos θ
  have hlog := (hasDerivAt_tanh θ).log ht.ne'
  have hcoeff : ((Real.cosh θ)⁻¹ ^ 2) / Real.tanh θ =
      1 / (Real.sinh θ * Real.cosh θ) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hs.ne', hc.ne']
  exact hlog.congr_deriv hcoeff

/-- The `θ`-partial derivative of the lower log strand coordinate. -/
theorem hasDerivAt_lowerLog_theta (θ χ : ℝ) (hθ : 0 < θ) :
    HasDerivAt (fun t : ℝ => lowerLogCoordinate t χ)
      (1 / (Real.sinh θ * Real.cosh θ)) θ := by
  dsimp [lowerLogCoordinate]
  exact (hasDerivAt_log_tanh θ hθ).sub_const χ

/-- The `χ`-partial derivative of the lower log strand coordinate. -/
theorem hasDerivAt_lowerLog_chi (θ χ : ℝ) :
    HasDerivAt (fun t : ℝ => lowerLogCoordinate θ t) (-1) χ := by
  dsimp [lowerLogCoordinate]
  have h := (hasDerivAt_const χ (Real.log (Real.tanh θ))).sub
    (hasDerivAt_id χ)
  have hfun : ((fun x : ℝ => Real.log (Real.tanh θ)) - id) =
      (fun t : ℝ => Real.log (Real.tanh θ) - t) := by
    funext t
    rfl
  rw [hfun] at h
  simpa using h

/-- The `θ`-partial derivative of the upper log strand coordinate. -/
theorem hasDerivAt_upperLog_theta (θ χ : ℝ) (hθ : 0 < θ) :
    HasDerivAt (fun t : ℝ => upperLogCoordinate t χ)
      (1 / (Real.sinh θ * Real.cosh θ)) θ := by
  dsimp [upperLogCoordinate]
  exact (hasDerivAt_log_tanh θ hθ).add_const χ

/-- The `χ`-partial derivative of the upper log strand coordinate. -/
theorem hasDerivAt_upperLog_chi (θ χ : ℝ) :
    HasDerivAt (fun t : ℝ => upperLogCoordinate θ t) 1 χ := by
  dsimp [upperLogCoordinate]
  have h := (hasDerivAt_const χ (Real.log (Real.tanh θ))).add
    (hasDerivAt_id χ)
  have hfun : ((fun x : ℝ => Real.log (Real.tanh θ)) + id) =
      (fun t : ℝ => Real.log (Real.tanh θ) + t) := by
    funext t
    rfl
  rw [hfun] at h
  simpa using h

/-- The determinant of the Jacobian of the two bare log strand coordinates
in `(θ, χ)` is `4 / sinh (2 θ)`. This is the actual calculus coefficient of
`d log w₋₊ ∧ d log w₊₋` on the positive-rapidity chart. -/
theorem bare_log_strand_jacobian (θ χ : ℝ) (hθ : 0 < θ) :
    deriv (fun t : ℝ => lowerLogCoordinate t χ) θ *
        deriv (fun t : ℝ => upperLogCoordinate θ t) χ -
      deriv (fun t : ℝ => lowerLogCoordinate θ t) χ *
        deriv (fun t : ℝ => upperLogCoordinate t χ) θ =
      4 / Real.sinh (2 * θ) := by
  rw [(hasDerivAt_lowerLog_theta θ χ hθ).deriv,
    (hasDerivAt_upperLog_chi θ χ).deriv,
    (hasDerivAt_lowerLog_chi θ χ).deriv,
    (hasDerivAt_upperLog_theta θ χ hθ).deriv]
  rw [Real.sinh_two_mul]
  field_simp [ne_of_gt (Real.sinh_pos_iff.mpr hθ),
    ne_of_gt (Real.cosh_pos θ)]
  ring

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

/-- Multiplying the log-strand Jacobian by the Plabic loop prefactor gives
the pulled-back coefficient `4 cosh (2θ) / sinh (2θ)`. -/
theorem loopPrefactor_mul_bare_log_jacobian (θ _χ : ℝ) :
    ((1 - loopWeight θ) / (1 + loopWeight θ)) *
      (4 / Real.sinh (2 * θ)) =
      4 * Real.cosh (2 * θ) / Real.sinh (2 * θ) := by
  rw [loopPrefactor_eq_cosh_two]
  ring

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
