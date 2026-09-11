import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FilteredHestenesKreinColimit
import InfoGeometry.Canonical.FilteredHestenesIteratedTransport

/-!
# Itakura--Saito cross-ratio readouts on the Hestenes--Krein colimit

This owner keeps the projective ratio in the real positive chart.  It proves
the finite scalar identity with the exponential Tomita deviance and transports
that readout through a Hestenes--Krein cone.  Complex unit-circle claims and
global analytic positivity are intentionally outside this owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinItakuraSaitoColimit

open InfoGeometry.Canonical.FilteredHestenesKreinColimit
open InfoGeometry.Krein

def realCrossRatio (s : ℝ) : ℝ := s / (1 - s)

def itakuraSaitoDeviance (u : ℝ) : ℝ :=
  u - Real.log u - 1

def modularTomitaDeviance (W : ℝ) : ℝ :=
  Real.exp W - 1 - W

theorem realCrossRatio_pos {s : ℝ} (hs : 0 < s) (hs_one : s < 1) :
    0 < realCrossRatio s := by
  unfold realCrossRatio
  exact div_pos hs (sub_pos.mpr hs_one)

theorem itakuraSaitoDeviance_exp (W : ℝ) :
    itakuraSaitoDeviance (Real.exp W) = modularTomitaDeviance W := by
  unfold itakuraSaitoDeviance modularTomitaDeviance
  rw [Real.log_exp]
  ring

theorem modularTomitaDeviance_nonneg (W : ℝ) :
    0 ≤ modularTomitaDeviance W := by
  unfold modularTomitaDeviance
  linarith [Real.add_one_le_exp W]

theorem itakuraSaitoDeviance_nonneg {u : ℝ} (hu : 0 < u) :
    0 ≤ itakuraSaitoDeviance u := by
  unfold itakuraSaitoDeviance
  linarith [Real.log_le_sub_one_of_pos hu]

theorem realCrossRatio_is_modularTomita (s : ℝ)
    (hs : 0 < s) (hs_one : s < 1) :
    itakuraSaitoDeviance (realCrossRatio s) =
      modularTomitaDeviance (Real.log (realCrossRatio s)) := by
  have hratio : Real.exp (Real.log (realCrossRatio s)) = realCrossRatio s :=
    Real.exp_log (realCrossRatio_pos hs hs_one)
  calc
    itakuraSaitoDeviance (realCrossRatio s) =
        itakuraSaitoDeviance (Real.exp (Real.log (realCrossRatio s))) := by
          rw [hratio]
    _ = modularTomitaDeviance (Real.log (realCrossRatio s)) :=
      itakuraSaitoDeviance_exp _

theorem realCrossRatio_is_nonneg (s : ℝ)
    (hs : 0 < s) (hs_one : s < 1) :
    0 ≤ itakuraSaitoDeviance (realCrossRatio s) :=
  itakuraSaitoDeviance_nonneg (realCrossRatio_pos hs hs_one)

theorem realCrossRatio_half : realCrossRatio (1 / 2 : ℝ) = 1 := by
  unfold realCrossRatio
  norm_num

/-- On the positive affine chart, the ratio-one point is uniquely the seam. -/
theorem realCrossRatio_eq_one_iff {s : ℝ}
    (hs : 0 < s) (hs_one : s < 1) :
    realCrossRatio s = 1 ↔ s = (1 / 2 : ℝ) := by
  constructor
  · intro h
    unfold realCrossRatio at h
    have hden : 1 - s ≠ 0 := ne_of_gt (sub_pos.mpr hs_one)
    field_simp [hden] at h
    linarith [hs]
  · intro h
    rw [h]
    exact realCrossRatio_half

theorem realCrossRatio_one_sub_inv {s : ℝ} (hs : 0 < s) (hs_one : s < 1) :
    realCrossRatio (1 - s) = (realCrossRatio s)⁻¹ := by
  unfold realCrossRatio
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hs_one_ne : 1 - s ≠ 0 := ne_of_gt (sub_pos.mpr hs_one)
  field_simp [hs_ne, hs_one_ne]
  ring

theorem itakuraSaitoDeviance_one : itakuraSaitoDeviance 1 = 0 := by
  norm_num [itakuraSaitoDeviance]

theorem realCrossRatio_seam_zero :
    itakuraSaitoDeviance (realCrossRatio (1 / 2 : ℝ)) = 0 := by
  rw [realCrossRatio_half, itakuraSaitoDeviance_one]

def weylSymmetricDeviance (u : ℝ) : ℝ :=
  (u - u⁻¹) ^ 2

theorem weylSymmetricDeviance_nonneg (u : ℝ) :
    0 ≤ weylSymmetricDeviance u := by
  unfold weylSymmetricDeviance
  exact sq_nonneg _

theorem weylSymmetricDeviance_one : weylSymmetricDeviance 1 = 0 := by
  norm_num [weylSymmetricDeviance]

theorem weylSymmetricDeviance_inv {u : ℝ} (hu : u ≠ 0) :
    weylSymmetricDeviance u⁻¹ = weylSymmetricDeviance u := by
  unfold weylSymmetricDeviance
  rw [inv_inv]
  field_simp [hu]
  ring

def stageItakuraSaitoReadout
    {C : HestenesKreinCone}
    (realCoordinate : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (n : ℕ) (x : DoubledSpace (C.Base n)) : ℝ :=
  itakuraSaitoDeviance (realCrossRatio (realCoordinate n x))

def limitItakuraSaitoReadout
    {C : HestenesKreinCone}
    (realCoordinate : DoubledSpace C.LimitBase → ℝ)
    (x : DoubledSpace C.LimitBase) : ℝ :=
  itakuraSaitoDeviance (realCrossRatio (realCoordinate x))

theorem stageItakuraSaitoReadout_eq_limit
    {C : HestenesKreinCone}
    (stageCoordinate : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (limitCoordinate : DoubledSpace C.LimitBase → ℝ)
    (hcoordinate : ∀ n x, stageCoordinate n x = limitCoordinate (C.ι n x))
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    stageItakuraSaitoReadout stageCoordinate n x =
      limitItakuraSaitoReadout limitCoordinate (C.ι n x) := by
  unfold stageItakuraSaitoReadout limitItakuraSaitoReadout
  rw [hcoordinate n x]

theorem stageItakuraSaitoReadout_nonneg
    {C : HestenesKreinCone}
    (stageCoordinate : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hpositive : ∀ n x, 0 < stageCoordinate n x ∧ stageCoordinate n x < 1)
    (n : ℕ) (x : DoubledSpace (C.Base n)) :
    0 ≤ stageItakuraSaitoReadout stageCoordinate n x := by
  unfold stageItakuraSaitoReadout
  exact realCrossRatio_is_nonneg (stageCoordinate n x)
    (hpositive n x).1 (hpositive n x).2

/-- The same positivity readout holds directly on the filtered limit carrier. -/
theorem limitItakuraSaitoReadout_nonneg
    {C : HestenesKreinCone}
    (limitCoordinate : DoubledSpace C.LimitBase → ℝ)
    (hpositive : ∀ x, 0 < limitCoordinate x ∧ limitCoordinate x < 1)
    (x : DoubledSpace C.LimitBase) :
    0 ≤ limitItakuraSaitoReadout limitCoordinate x := by
  unfold limitItakuraSaitoReadout
  exact realCrossRatio_is_nonneg (limitCoordinate x)
    (hpositive x).1 (hpositive x).2

theorem stageItakuraSaitoReadout_bondIterate_eq
    {C : HestenesKreinCone}
    (readout : ∀ n, DoubledSpace (C.Base n) → ℝ)
    (hreadout : ∀ n m x,
      readout (n + m) (C.toFilteredPhaseCone.bondIterate n m x) =
        readout n x)
    (n m : ℕ) (x : DoubledSpace (C.Base n)) :
    readout (n + m) (C.toFilteredPhaseCone.bondIterate n m x) =
      readout n x :=
  hreadout n m x

end InfoGeometry.Canonical.HestenesKreinItakuraSaitoColimit

end noncomputable section
