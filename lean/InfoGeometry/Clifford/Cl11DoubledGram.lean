/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorExactCurvatureTrace
import InfoGeometry.CliffordWeyl.RealDoubledIdealMetric

/-!
# Definite doubled Gram forms on the actual real matrix colimit

`Limit` is the existing algebraic direct limit, not a Hilbert completion.
Its established faithful positive trace proves that a sum of two transpose
squares vanishes only when both entries vanish. The result applies to the
whole doubled module and to full `2 × 2` matrices over this infinite algebra.
No commutativity of entries or scalar spectral reduction is used.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11DoubledGram

open Matrix InfoGeometry.Physics
open Cl11TensorTowerLimit
open InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
open InfoGeometry.Canonical.TensorExactCurvatureTrace
open InfoGeometry.CliffordWeyl.RealDoubledIdealMetric
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

/-- Faithfulness for the two summands is inherited from the actual colimit trace. -/
theorem two_star_squares_eq_zero_iff (x y : Limit) :
    star x * x + star y * y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have ht := congrArg normalizedTraceLimit h
    rw [map_add, map_zero] at ht
    have hx := normalizedTraceLimit_star_mul_self_nonneg x
    have hy := normalizedTraceLimit_star_mul_self_nonneg y
    constructor
    · apply (normalizedTraceLimit_star_mul_self_eq_zero_iff x).mp
      linarith
    · apply (normalizedTraceLimit_star_mul_self_eq_zero_iff y).mp
      linarith
  · rintro ⟨rfl, rfl⟩
    simp

/-- The ring-valued Gram form on the actual doubled module is definite. -/
theorem column_gram_eq_zero_iff (v : Fin 2 → Limit) :
    star v ⬝ᵥ v = 0 ↔ v = 0 := by
  simp only [dotProduct, Fin.sum_univ_two]
  rw [two_star_squares_eq_zero_iff]
  constructor
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
  · intro h
    simp [h]

theorem column_gram_trace_nonneg (v : Fin 2 → Limit) :
    0 ≤ normalizedTraceLimit (star v ⬝ᵥ v) := by
  simp only [dotProduct, Fin.sum_univ_two, map_add]
  exact add_nonneg (normalizedTraceLimit_star_mul_self_nonneg _)
    (normalizedTraceLimit_star_mul_self_nonneg _)

/-- Native matrix star is proper on full doubled operators over the colimit. -/
theorem matrix_star_mul_self_eq_zero_iff (X : BdGBlock Limit) :
    star X * X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hcol (j : Fin 2) : X 0 j = 0 ∧ X 1 j = 0 := by
      apply (two_star_squares_eq_zero_iff _ _).mp
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] using
        congrArg (fun M : BdGBlock Limit => M j j) h
    ext i j
    fin_cases i
    · exact (hcol j).1
    · exact (hcol j).2
  · intro h
    simp [h]

/-- Metric cancellation and faithful algebraic positivity are separate
premises in the construction, joined here on the concrete infinite carrier. -/
theorem doubled_metric_gram_eq_zero_iff (η : Limit) (hη : η * η = 1)
    (v : Fin 2 → Limit) :
    bilinear (doubledMetric η) (doubledMetric η) v v = 0 ↔ v = 0 := by
  rw [doubled_bilinear_cancel η hη, column_gram_eq_zero_iff]

theorem doubled_metric_gram_trace_nonneg (η : Limit) (hη : η * η = 1)
    (v : Fin 2 → Limit) :
    0 ≤ normalizedTraceLimit (bilinear (doubledMetric η) (doubledMetric η) v v) := by
  rw [doubled_bilinear_cancel η hη]
  exact column_gram_trace_nonneg v

/-- The correctly typed operator-ideal untwisting is definite as well. -/
theorem matrix_metric_sharp_gram_eq_zero_iff (G X : BdGBlock Limit)
    (hG : G * G = 1) :
    G * (InfoGeometry.Canonical.SpinorialCore.Krein.sharp G X * G * X) = 0 ↔
      X = 0 := by
  rw [metric_sharp_metric_product G X X hG, matrix_star_mul_self_eq_zero_iff]

end InfoGeometry.Clifford.Cl11DoubledGram
