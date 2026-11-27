/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.SmoothedMangoldtInterpolation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Integer and real growth bounds for the centered Mangoldt sum

For either fixed sign and any nonnegative exponent, an eventual power bound at
integers transfers to real cutoffs with the explicit constant
`2 ^ alpha * C + 1 / 8`. Restriction to integers gives the converse. The same
equivalence is then specialized to the square-root-plus-epsilon scale, keeping
the sign fixed outside the epsilon quantifier.

These are equivalences of explicit hypotheses. No arithmetic cancellation
bound, Landau theorem, or Riemann Hypothesis is proved by this module.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeDistributionLaw

/-- An eventual one-sided power bound at natural cutoffs. -/
def IntegerCenteredMangoldtPowerBound (sign alpha : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N →
      sign * centeredSmoothedMangoldtSum (N : ℝ) ≤ C * (N : ℝ) ^ alpha

/-- An eventual one-sided power bound at real cutoffs. -/
def RealCenteredMangoldtPowerBound (sign alpha : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℝ, 1 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      sign * centeredSmoothedMangoldtSum x ≤ C * x ^ alpha

/-- The signed square-root-plus-epsilon growth hypothesis at integers. -/
def IntegerCenteredMangoldtSqrtBound (sign : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    IntegerCenteredMangoldtPowerBound sign ((1 : ℝ) / 2 + epsilon)

/-- The signed square-root-plus-epsilon growth hypothesis at real cutoffs. -/
def RealCenteredMangoldtSqrtBound (sign : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    RealCenteredMangoldtPowerBound sign ((1 : ℝ) / 2 + epsilon)

/-- Explicit transfer of a one-sided integer bound to every real cutoff beyond
the same threshold. The interpolation loss is at most `x ^ alpha / 8`. -/
theorem centeredSmoothedMangoldtSum_real_bound_of_integer_bound
    {sign alpha C : ℝ} (hsign : sign = 1 ∨ sign = -1)
    (halpha : 0 ≤ alpha) (hC : 0 ≤ C) {N₀ : ℕ} (hN₀ : 1 ≤ N₀)
    (hbound : ∀ N : ℕ, N₀ ≤ N →
      sign * centeredSmoothedMangoldtSum (N : ℝ) ≤ C * (N : ℝ) ^ alpha)
    {x : ℝ} (hx : (N₀ : ℝ) ≤ x) :
    sign * centeredSmoothedMangoldtSum x ≤
      ((2 : ℝ) ^ alpha * C + 1 / 8) * x ^ alpha := by
  let N : ℕ := ⌊x⌋₊
  let t : ℝ := x - (N : ℝ)
  have hN₀real : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
  have hx1 : 1 ≤ x := hN₀real.trans hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hNlarge : N₀ ≤ N := Nat.le_floor hx
  have hN : 1 ≤ N := hN₀.trans hNlarge
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have ht0 : 0 ≤ t := sub_nonneg.mpr hNx
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have hpoint : (N : ℝ) + t = x := by dsimp [t]; ring
  have hnext : ((N + 1 : ℕ) : ℝ) ≤ 2 * x := by
    push_cast
    linarith
  have hpowN : (N : ℝ) ^ alpha ≤ (2 * x) ^ alpha :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) halpha
  have hpowNext : (((N + 1 : ℕ) : ℝ)) ^ alpha ≤ (2 * x) ^ alpha :=
    Real.rpow_le_rpow (Nat.cast_nonneg (N + 1)) hnext halpha
  have hleft : sign * centeredSmoothedMangoldtSum (N : ℝ) ≤
      C * (2 * x) ^ alpha :=
    (hbound N hNlarge).trans (mul_le_mul_of_nonneg_left hpowN hC)
  have hright : sign * centeredSmoothedMangoldtSum ((N + 1 : ℕ) : ℝ) ≤
      C * (2 * x) ^ alpha :=
    (hbound (N + 1) (hNlarge.trans (Nat.le_succ N))).trans
      (mul_le_mul_of_nonneg_left hpowNext hC)
  have haffine : (1 - t) * (sign * centeredSmoothedMangoldtSum (N : ℝ)) +
        t * (sign * centeredSmoothedMangoldtSum ((N + 1 : ℕ) : ℝ)) ≤
      C * (2 * x) ^ alpha := by
    calc
      _ ≤ (1 - t) * (C * (2 * x) ^ alpha) + t * (C * (2 * x) ^ alpha) :=
        add_le_add (mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr ht1))
          (mul_le_mul_of_nonneg_left hright ht0)
      _ = C * (2 * x) ^ alpha := by ring
  have herror : 1 / (8 * (N : ℝ)) ≤ (1 / 8 : ℝ) * x ^ alpha := by
    calc
      1 / (8 * (N : ℝ)) ≤ (1 / 8 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      _ ≤ (1 / 8 : ℝ) * x ^ alpha := by
        nlinarith [Real.one_le_rpow hx1 halpha]
  have hinterp := signed_centeredSmoothedMangoldtSum_le_affine hN hsign t ht0 ht1
  rw [hpoint] at hinterp
  calc
    sign * centeredSmoothedMangoldtSum x ≤
        C * (2 * x) ^ alpha + 1 / (8 * (N : ℝ)) :=
      hinterp.trans (add_le_add haffine le_rfl)
    _ ≤ C * (2 * x) ^ alpha + (1 / 8 : ℝ) * x ^ alpha :=
      add_le_add le_rfl herror
    _ = ((2 : ℝ) ^ alpha * C + 1 / 8) * x ^ alpha := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0]
      ring

/-- The existence form of the explicit integer-to-real estimate. -/
theorem realCenteredMangoldtPowerBound_of_integer {sign alpha : ℝ}
    (hsign : sign = 1 ∨ sign = -1) (halpha : 0 ≤ alpha)
    (h : IntegerCenteredMangoldtPowerBound sign alpha) :
    RealCenteredMangoldtPowerBound sign alpha := by
  obtain ⟨C, hC, N₀, hN₀, hbound⟩ := h
  refine ⟨(2 : ℝ) ^ alpha * C + 1 / 8, by positivity, (N₀ : ℝ), ?_, ?_⟩
  · exact_mod_cast hN₀
  · intro x hx
    exact centeredSmoothedMangoldtSum_real_bound_of_integer_bound
      hsign halpha hC hN₀ hbound hx

/-- Restriction of a real-cutoff bound to sufficiently large integers. -/
theorem integerCenteredMangoldtPowerBound_of_real {sign alpha : ℝ}
    (h : RealCenteredMangoldtPowerBound sign alpha) :
    IntegerCenteredMangoldtPowerBound sign alpha := by
  obtain ⟨C, hC, x₀, hx₀, hbound⟩ := h
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge x₀
  refine ⟨C, hC, N₀, ?_, ?_⟩
  · exact_mod_cast hx₀.trans hN₀
  · intro N hN
    exact hbound (N : ℝ) (hN₀.trans (by exact_mod_cast hN))

/-- Integer and real one-sided power bounds are equivalent for either sign. -/
theorem integerCenteredMangoldtPowerBound_iff_real {sign alpha : ℝ}
    (hsign : sign = 1 ∨ sign = -1) (halpha : 0 ≤ alpha) :
    IntegerCenteredMangoldtPowerBound sign alpha ↔
      RealCenteredMangoldtPowerBound sign alpha :=
  ⟨realCenteredMangoldtPowerBound_of_integer hsign halpha,
    integerCenteredMangoldtPowerBound_of_real⟩

/-- At the square-root-plus-epsilon scale, integer cutoffs suffice. The sign is
fixed before quantifying over epsilon, and constants may depend on epsilon. -/
theorem integerCenteredMangoldtSqrtBound_iff_real {sign : ℝ}
    (hsign : sign = 1 ∨ sign = -1) :
    IntegerCenteredMangoldtSqrtBound sign ↔ RealCenteredMangoldtSqrtBound sign := by
  constructor
  · intro h epsilon hepsilon
    exact realCenteredMangoldtPowerBound_of_integer hsign (by linarith)
      (h epsilon hepsilon)
  · intro h epsilon hepsilon
    exact integerCenteredMangoldtPowerBound_of_real (h epsilon hepsilon)

end InfoGeometry.Arithmetic.PrimeDistributionLaw
