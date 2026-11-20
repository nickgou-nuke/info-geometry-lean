/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Mellin integral of a ramp kernel

For `a > 0` and `1 < s.re`, the positive-part ramp `max (x / a - 1) 0`
has an absolutely integrable weighted kernel. Its integral is
`a ^ (-s) / (s * (s - 1))`. When `1 ≤ a`, the same formula holds on `(1, ∞)`.

The proof reduces the ramp to an indicator supported on `(a, ∞)`, then applies
Mathlib's improper complex-power integrals. Integrability is proved explicitly
before the integral formula is used. No coefficient estimate, series/integral
interchange, analytic continuation, or zeta nonvanishing premise occurs here.
-/

noncomputable section

open Set MeasureTheory

namespace InfoGeometry.Analysis.SmoothedMellinKernel

/-- The complex Mellin weight attached to the positive-part affine ramp. -/
def rampMellinIntegrand (a : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  (↑(max (x / a - 1) 0) : ℂ) * (x : ℂ) ^ (-s - 1)

/-- Above its cutoff the ramp is a difference of two complex powers; below the
cutoff it vanishes. This is a pointwise identity on the whole real line. -/
theorem rampMellinIntegrand_eq_indicator {a : ℝ} (ha : 0 < a) (s : ℂ) :
    rampMellinIntegrand a s =
      (Ioi a).indicator
        (fun x : ℝ => (a : ℂ)⁻¹ * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)) := by
  classical
  funext x
  dsimp only [rampMellinIntegrand]
  by_cases hax : a < x
  · have hratio : 0 ≤ x / a - 1 :=
      sub_nonneg.mpr ((le_div_iff₀ ha).mpr (by simpa using hax.le))
    have hx : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ha.trans hax).ne'
    have hpower : (x : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (-s) := by
      calc
        (x : ℂ) * (x : ℂ) ^ (-s - 1) = (x : ℂ) ^ (1 + (-s - 1)) := by
          rw [Complex.cpow_add _ _ hx, Complex.cpow_one]
        _ = (x : ℂ) ^ (-s) := by
          congr 1
          ring
    rw [Set.indicator_of_mem (s := Ioi a) hax, max_eq_left hratio]
    simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one]
    calc
      ((x : ℂ) / (a : ℂ) - 1) * (x : ℂ) ^ (-s - 1) =
          (a : ℂ)⁻¹ * ((x : ℂ) * (x : ℂ) ^ (-s - 1)) - (x : ℂ) ^ (-s - 1) := by
            simp only [div_eq_mul_inv]
            ring
      _ = (a : ℂ)⁻¹ * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1) := by rw [hpower]
  · have hratio : x / a - 1 ≤ 0 :=
      sub_nonpos.mpr ((div_le_iff₀ ha).mpr (by simpa using le_of_not_gt hax))
    simp only [Set.indicator_of_notMem (s := Ioi a) hax, max_eq_right hratio,
      Complex.ofReal_zero, zero_mul]

/-- Absolute integrability of the weighted ramp on the whole real line. -/
theorem integrable_rampMellinIntegrand {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 1 < s.re) : Integrable (rampMellinIntegrand a s) := by
  have hneg : (-s).re < -1 := by simpa only [Complex.neg_re] using neg_lt_neg hs
  have hshift : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [rampMellinIntegrand_eq_indicator ha s]
  have hdiff : IntegrableOn
      (fun x : ℝ => (a : ℂ)⁻¹ * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)) (Ioi a) :=
    ((integrableOn_Ioi_cpow_of_lt hneg ha).const_mul ((a : ℂ)⁻¹)).sub
      (integrableOn_Ioi_cpow_of_lt hshift ha)
  exact hdiff.integrable_indicator measurableSet_Ioi

/-- The complete ramp integral, with its convergence hypotheses exposed. -/
theorem integral_rampMellinIntegrand {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 1 < s.re) :
    (∫ x : ℝ, rampMellinIntegrand a s x) = (a : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hneg : (-s).re < -1 := by simpa only [Complex.neg_re] using neg_lt_neg hs
  have hshift : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at hs
  rw [rampMellinIntegrand_eq_indicator ha s,
    integral_indicator measurableSet_Ioi,
    integral_sub ((integrableOn_Ioi_cpow_of_lt hneg ha).const_mul _)
      (integrableOn_Ioi_cpow_of_lt hshift ha),
    integral_const_mul, integral_Ioi_cpow_of_lt hneg ha,
    integral_Ioi_cpow_of_lt hshift ha]
  rw [sub_add_cancel, Complex.cpow_add (-s) 1 haC, Complex.cpow_one]
  rw [show -s + 1 = -(s - 1) by ring]
  field_simp [haC, hs0, sub_ne_zero.mpr hs1]
  ring

/-- Convergence on `(1, ∞)` in the form used by smoothed arithmetic sums. -/
theorem integrableOn_Ioi_one_rampMellinIntegrand {a : ℝ} (ha : 1 ≤ a) {s : ℂ}
    (hs : 1 < s.re) : IntegrableOn (rampMellinIntegrand a s) (Ioi 1) :=
  (integrable_rampMellinIntegrand (zero_lt_one.trans_le ha) hs).integrableOn

/-- A cutoff at least one gives the Mellin kernel on `(1, ∞)`. -/
theorem integral_Ioi_one_rampMellinIntegrand {a : ℝ} (ha : 1 ≤ a) {s : ℂ}
    (hs : 1 < s.re) :
    (∫ x : ℝ in Ioi 1, rampMellinIntegrand a s x) =
      (a : ℂ) ^ (-s) / (s * (s - 1)) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  calc
    (∫ x : ℝ in Ioi 1, rampMellinIntegrand a s x) =
        ∫ x : ℝ, rampMellinIntegrand a s x := by
      rw [rampMellinIntegrand_eq_indicator ha0 s,
        setIntegral_indicator measurableSet_Ioi,
        inter_eq_right.mpr (Ioi_subset_Ioi ha),
        integral_indicator measurableSet_Ioi]
    _ = (a : ℂ) ^ (-s) / (s * (s - 1)) := integral_rampMellinIntegrand ha0 hs

end InfoGeometry.Analysis.SmoothedMellinKernel
