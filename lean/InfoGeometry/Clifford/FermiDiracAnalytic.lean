/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Real Fermi occupation and single-mode Massieu calculus

The scalar Fermi API below is extracted unchanged from
`ChiralGrandCanonicalThermalGeometry`, preserving its namespace and consumers.
The additional results concern the real, dimensionless parameter `x` and the
single-mode occupation `fermiOccupation 1 x`. Binary entropy uses Mathlib's
native `Real.binEntropy`.
-/

noncomputable section

namespace InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry

/-- The Fermi occupation readout of a native mode energy. -/
def fermiOccupation (β ξ : ℝ) : ℝ :=
  1 / (Real.exp (β * ξ) + 1)

/-- The logistic coordinate on the open one-simplex. -/
def fermiSimplexCoordinate (θ : ℝ) : ℝ :=
  Real.exp θ / (Real.exp θ + 1)

theorem fermiSimplexCoordinate_pos (θ : ℝ) :
    0 < fermiSimplexCoordinate θ := by
  unfold fermiSimplexCoordinate
  exact div_pos (Real.exp_pos _) (by positivity)

theorem fermiSimplexCoordinate_lt_one (θ : ℝ) :
    fermiSimplexCoordinate θ < 1 := by
  unfold fermiSimplexCoordinate
  have hden : 0 < Real.exp θ + 1 := by positivity
  apply (div_lt_iff₀ hden).2
  linarith

theorem fermiSimplexCoordinate_add_complement (θ : ℝ) :
    fermiSimplexCoordinate θ + 1 / (Real.exp θ + 1) = 1 := by
  unfold fermiSimplexCoordinate
  have hden : Real.exp θ + 1 ≠ 0 :=
    by positivity
  field_simp [hden]

theorem fermiSimplexCoordinate_crossRatio (θ : ℝ) :
    fermiSimplexCoordinate θ /
        (1 - fermiSimplexCoordinate θ) = Real.exp θ := by
  unfold fermiSimplexCoordinate
  have hden : Real.exp θ + 1 ≠ 0 :=
    by positivity
  have hcomp :
      1 - Real.exp θ / (Real.exp θ + 1) =
        1 / (Real.exp θ + 1) := by
    field_simp [hden]
    ring
  rw [hcomp]
  field_simp [hden]

theorem fermiSimplexCoordinate_neg (θ : ℝ) :
    fermiSimplexCoordinate (-θ) = 1 - fermiSimplexCoordinate θ := by
  unfold fermiSimplexCoordinate
  rw [Real.exp_neg]
  have hexp : Real.exp θ ≠ 0 := Real.exp_ne_zero _
  have hden : Real.exp θ + 1 ≠ 0 :=
    by positivity
  field_simp [hexp, hden]
  ring

@[simp] theorem fermiSimplexCoordinate_zero :
    fermiSimplexCoordinate 0 = 1 / 2 := by
  norm_num [fermiSimplexCoordinate]

theorem fermiOccupation_eq_fermiSimplexCoordinate (β ξ : ℝ) :
    fermiOccupation β ξ = fermiSimplexCoordinate (-(β * ξ)) := by
  unfold fermiOccupation fermiSimplexCoordinate
  rw [Real.exp_neg]
  have hexp : Real.exp (β * ξ) ≠ 0 := Real.exp_ne_zero _
  have hden : Real.exp (β * ξ) + 1 ≠ 0 :=
    by positivity
  field_simp [hexp, hden]
  ring

/-- Occupation odds, with no alteration of the underlying CAR algebra. -/
def occupationOdds (β ξ : ℝ) : ℝ :=
  fermiOccupation β ξ / (1 - fermiOccupation β ξ)

lemma exp_add_one_pos (β ξ : ℝ) :
    0 < Real.exp (β * ξ) + 1 := by
  exact add_pos_of_nonneg_of_pos (le_of_lt (Real.exp_pos _)) zero_lt_one

theorem fermiOccupation_add_complement (β ξ : ℝ) :
    fermiOccupation β ξ +
        Real.exp (β * ξ) / (Real.exp (β * ξ) + 1) = 1 := by
  unfold fermiOccupation
  have h := exp_add_one_pos β ξ
  field_simp [ne_of_gt h]
  ring

theorem occupationOdds_eq_exp_neg (β ξ : ℝ) :
    occupationOdds β ξ = Real.exp (-(β * ξ)) := by
  unfold occupationOdds fermiOccupation
  have h : Real.exp (β * ξ) + 1 ≠ 0 :=
    ne_of_gt (exp_add_one_pos β ξ)
  have hcomp : 1 - 1 / (Real.exp (β * ξ) + 1) =
      Real.exp (β * ξ) / (Real.exp (β * ξ) + 1) := by
    field_simp [h]
    ring
  rw [hcomp]
  field_simp [h, Real.exp_ne_zero]
  rw [Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero _)]

theorem occupationOdds_pos (β ξ : ℝ) :
    0 < occupationOdds β ξ := by
  rw [occupationOdds_eq_exp_neg]
  exact Real.exp_pos _

/-! ## Dimensionless occupation and the half-occupation threshold -/

theorem fermiOccupation_pos (β ξ : ℝ) : 0 < fermiOccupation β ξ := by
  rw [fermiOccupation_eq_fermiSimplexCoordinate]
  exact fermiSimplexCoordinate_pos _

theorem fermiOccupation_lt_one (β ξ : ℝ) : fermiOccupation β ξ < 1 := by
  rw [fermiOccupation_eq_fermiSimplexCoordinate]
  exact fermiSimplexCoordinate_lt_one _

theorem fermiOccupation_one_eq_weight (x : ℝ) :
    fermiOccupation 1 x = Real.exp (-x) / (1 + Real.exp (-x)) := by
  rw [fermiOccupation_eq_fermiSimplexCoordinate]
  simp [fermiSimplexCoordinate, add_comm]

theorem fermiOccupation_one_neg (x : ℝ) :
    fermiOccupation 1 (-x) = 1 - fermiOccupation 1 x := by
  rw [fermiOccupation_eq_fermiSimplexCoordinate,
    fermiOccupation_eq_fermiSimplexCoordinate]
  simp only [one_mul]
  exact fermiSimplexCoordinate_neg (-x)

@[simp] theorem fermiOccupation_one_zero : fermiOccupation 1 0 = 1 / 2 := by
  norm_num [fermiOccupation]

theorem fermiOccupation_one_eq_half_iff (x : ℝ) :
    fermiOccupation 1 x = 1 / 2 ↔ x = 0 := by
  have hden : Real.exp x + 1 ≠ 0 := by positivity
  unfold fermiOccupation
  simp only [one_mul]
  rw [div_eq_div_iff hden (by norm_num : (2 : ℝ) ≠ 0)]
  constructor
  · intro h
    exact (Real.exp_eq_one_iff x).mp (by linarith)
  · intro h
    subst x
    norm_num

theorem fermiOccupation_one_lt_half_iff (x : ℝ) :
    fermiOccupation 1 x < 1 / 2 ↔ 0 < x := by
  have hden : 0 < Real.exp x + 1 := by positivity
  unfold fermiOccupation
  simp only [one_mul]
  rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
  constructor
  · intro h
    exact Real.one_lt_exp_iff.mp (by linarith)
  · intro h
    have he := Real.one_lt_exp_iff.mpr h
    linarith

theorem half_lt_fermiOccupation_one_iff (x : ℝ) :
    1 / 2 < fermiOccupation 1 x ↔ x < 0 := by
  have hden : 0 < Real.exp x + 1 := by positivity
  unfold fermiOccupation
  simp only [one_mul]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hden]
  constructor
  · intro h
    exact Real.exp_lt_one_iff.mp (by linarith)
  · intro h
    have he := Real.exp_lt_one_iff.mpr h
    linarith

/-! ## The Massieu potential and its native derivatives -/

/-- The log-partition potential of a two-state mode with weights `exp(-x), 1`. -/
def fermiMassieu (x : ℝ) : ℝ := Real.log (1 + Real.exp (-x))

/-- Variance of the occupied-state indicator in the two-state mode. -/
def fermiSusceptibility (x : ℝ) : ℝ :=
  fermiOccupation 1 x * (1 - fermiOccupation 1 x)

theorem hasDerivAt_fermiOccupation_one (x : ℝ) :
    HasDerivAt (fermiOccupation 1) (-fermiSusceptibility x) x := by
  have hden : Real.exp x + 1 ≠ 0 := by positivity
  have h := ((Real.hasDerivAt_exp x).add_const 1).inv hden
  convert h using 1
  · funext y
    simp [fermiOccupation, one_div]
  · unfold fermiSusceptibility fermiOccupation
    simp only [one_mul]
    field_simp [hden]
    ring

theorem deriv_fermiOccupation_one (x : ℝ) :
    deriv (fermiOccupation 1) x = -fermiSusceptibility x :=
  (hasDerivAt_fermiOccupation_one x).deriv

theorem hasDerivAt_fermiMassieu (x : ℝ) :
    HasDerivAt fermiMassieu (-fermiOccupation 1 x) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1
    · funext y
      rfl
    · ring
  have hden : 1 + Real.exp (-x) ≠ 0 := by positivity
  have h := (hexp.const_add 1).log hden
  have hread : Real.exp (-x) / (1 + Real.exp (-x)) = fermiOccupation 1 x :=
    (fermiOccupation_one_eq_weight x).symm
  change HasDerivAt fermiMassieu
    (-Real.exp (-x) / (1 + Real.exp (-x))) x at h
  simpa only [neg_div, hread] using h

theorem deriv_fermiMassieu (x : ℝ) :
    deriv fermiMassieu x = -fermiOccupation 1 x :=
  (hasDerivAt_fermiMassieu x).deriv

theorem hasDerivAt_deriv_fermiMassieu (x : ℝ) :
    HasDerivAt (deriv fermiMassieu) (fermiSusceptibility x) x := by
  have hfun : deriv fermiMassieu = fun y => -fermiOccupation 1 y := by
    funext y
    exact deriv_fermiMassieu y
  rw [hfun]
  convert (hasDerivAt_fermiOccupation_one x).neg using 1
  ring

theorem deriv2_fermiMassieu (x : ℝ) :
    deriv (deriv fermiMassieu) x = fermiSusceptibility x :=
  (hasDerivAt_deriv_fermiMassieu x).deriv

theorem fermiSusceptibility_pos (x : ℝ) : 0 < fermiSusceptibility x :=
  mul_pos (fermiOccupation_pos 1 x) (sub_pos.mpr (fermiOccupation_lt_one 1 x))

/-- The exact square defect determines the unique susceptibility maximum. -/
theorem fermiSusceptibility_defect (x : ℝ) :
    1 / 4 - fermiSusceptibility x = (fermiOccupation 1 x - 1 / 2) ^ 2 := by
  unfold fermiSusceptibility
  ring

theorem fermiSusceptibility_le_quarter (x : ℝ) : fermiSusceptibility x ≤ 1 / 4 := by
  have h := sq_nonneg (fermiOccupation 1 x - 1 / 2)
  rw [← fermiSusceptibility_defect] at h
  linarith

theorem fermiSusceptibility_eq_quarter_iff (x : ℝ) :
    fermiSusceptibility x = 1 / 4 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (fermiOccupation 1 x - 1 / 2) ^ 2 = 0 := by
      rw [← fermiSusceptibility_defect, h]
      ring
    have hp : fermiOccupation 1 x = 1 / 2 := by
      nlinarith [sq_nonneg (fermiOccupation 1 x - 1 / 2)]
    exact (fermiOccupation_one_eq_half_iff x).mp hp
  · rintro rfl
    norm_num [fermiSusceptibility]

theorem fermiSusceptibility_neg (x : ℝ) :
    fermiSusceptibility (-x) = fermiSusceptibility x := by
  unfold fermiSusceptibility
  rw [fermiOccupation_one_neg]
  ring

/-! ## Binary entropy and its unique maximum -/

theorem fermiEntropy_pos (x : ℝ) : 0 < Real.binEntropy (fermiOccupation 1 x) :=
  Real.binEntropy_pos (fermiOccupation_pos 1 x) (fermiOccupation_lt_one 1 x)

theorem fermiEntropy_le_log_two (x : ℝ) :
    Real.binEntropy (fermiOccupation 1 x) ≤ Real.log 2 :=
  Real.binEntropy_le_log_two

theorem fermiEntropy_eq_log_two_iff (x : ℝ) :
    Real.binEntropy (fermiOccupation 1 x) = Real.log 2 ↔ x = 0 := by
  rw [Real.binEntropy_eq_log_two]
  simpa only [one_div] using fermiOccupation_one_eq_half_iff x

theorem fermiEntropy_neg (x : ℝ) :
    Real.binEntropy (fermiOccupation 1 (-x)) =
      Real.binEntropy (fermiOccupation 1 x) := by
  rw [fermiOccupation_one_neg, Real.binEntropy_one_sub]

/-- The two-state Gibbs identity `S = log Z + x n` in native binary entropy. -/
theorem fermiEntropy_eq_massieu_add (x : ℝ) :
    Real.binEntropy (fermiOccupation 1 x) =
      fermiMassieu x + x * fermiOccupation 1 x := by
  have hden : 1 + Real.exp (-x) ≠ 0 := by positivity
  have hp : Real.log (fermiOccupation 1 x) = -x - fermiMassieu x := by
    rw [fermiOccupation_one_eq_weight,
      Real.log_div (Real.exp_ne_zero _) hden, Real.log_exp]
    rfl
  have hcomp : 1 - fermiOccupation 1 x = (1 + Real.exp (-x))⁻¹ := by
    rw [fermiOccupation_one_eq_weight]
    field_simp [hden]
    ring
  have hq : Real.log (1 - fermiOccupation 1 x) = -fermiMassieu x := by
    rw [hcomp, Real.log_inv]
    rfl
  rw [Real.binEntropy, Real.log_inv, Real.log_inv, hp, hq]
  ring

/-- The entropy derivative changes sign only at zero co-rotating exponent. -/
theorem hasDerivAt_fermiEntropy (x : ℝ) :
    HasDerivAt (fun y => Real.binEntropy (fermiOccupation 1 y))
      (-x * fermiSusceptibility x) x := by
  have hfun : (fun y => Real.binEntropy (fermiOccupation 1 y)) =
      fun y => fermiMassieu y + y * fermiOccupation 1 y := by
    funext y
    exact fermiEntropy_eq_massieu_add y
  rw [hfun]
  convert (hasDerivAt_fermiMassieu x).add
    ((hasDerivAt_id x).mul (hasDerivAt_fermiOccupation_one x)) using 1
  · funext y
    rfl
  · simp only [id_eq]
    ring

end InfoGeometry.Clifford.ChiralGrandCanonicalThermalGeometry
