/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble
import InfoGeometry.CliffordWeyl.DiracSolderOperatorAction
import InfoGeometry.Canonical.SpinorialCore.KreinAdjoint
import Mathlib.LinearAlgebra.Pi

/-!
# Real doubled matrices, ideal support, and metric cancellation

The columns are `Fin 2 → B`, equivalent to the actual product `B × B`.
All matrix coefficients remain in the possibly noncommutative ring `B`.
The matrix/pair dictionary is real-linear when `B` is a real algebra; left
matrix multiplication is not asserted to be left-`B`-linear.

Cancelling an involutive metric is an algebraic identity. Positivity for the
concrete real matrix colimit is proved separately in `Cl11DoubledGram`.
-/

namespace InfoGeometry.CliffordWeyl.RealDoubledIdealMetric

open Matrix InfoGeometry.Physics
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

variable {B : Type*} [Ring B]

/-- The internal square-minus-one matrix, with an explicit ordered product. -/
def phaseMatrix : BdGBlock B := chiralGrading * andreevSwap

theorem phaseMatrix_eq : phaseMatrix (B := B) = !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseMatrix, chiralGrading, andreevSwap, Matrix.mul_apply, Fin.sum_univ_two]

theorem phaseMatrix_sq : phaseMatrix (B := B) * phaseMatrix = -1 := by
  rw [phaseMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem swap_grading_eq_neg_phase :
    andreevSwap (A := B) * chiralGrading = -phaseMatrix := by
  rw [phaseMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralGrading, andreevSwap, Matrix.mul_apply, Fin.sum_univ_two]

/-- Changing the order of the two involutions changes the triple product. -/
theorem swap_grading_phase_eq_one :
    andreevSwap (A := B) * chiralGrading * phaseMatrix = 1 := by
  rw [swap_grading_eq_neg_phase, neg_mul, phaseMatrix_sq, neg_neg]

theorem grading_swap_phase_eq_neg_one :
    chiralGrading (A := B) * andreevSwap * phaseMatrix = -1 :=
  phaseMatrix_sq

section PairDictionary

variable [Algebra ℝ B]

open InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble

/-- Native columns and actual doubled module operators describe the same swap. -/
theorem finTwoArrow_swap (v : Fin 2 → B) :
    LinearEquiv.finTwoArrow ℝ B (andreevSwap *ᵥ v) =
      swapOp (R := ℝ) (LinearEquiv.finTwoArrow ℝ B v) := by
  ext <;> simp [LinearEquiv.finTwoArrow, andreevSwap, swapOp,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem finTwoArrow_grading (v : Fin 2 → B) :
    LinearEquiv.finTwoArrow ℝ B (chiralGrading *ᵥ v) =
      gradingOp (R := ℝ) (LinearEquiv.finTwoArrow ℝ B v) := by
  ext <;> simp [LinearEquiv.finTwoArrow, chiralGrading, gradingOp,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The existing endomorphism phase uses the opposite sign convention. -/
theorem finTwoArrow_phase (v : Fin 2 → B) :
    LinearEquiv.finTwoArrow ℝ B (phaseMatrix *ᵥ v) =
      -phaseOp (R := ℝ) (LinearEquiv.finTwoArrow ℝ B v) := by
  rw [phaseMatrix_eq]
  ext <;> simp [LinearEquiv.finTwoArrow, phaseOp_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end PairDictionary

/-- Arbitrary left matrix actions preserve two copies of the same left ideal. -/
theorem mulVec_preserves_right_support (M : BdGBlock B) (v : Fin 2 → B)
    (p : B) (hv : ∀ i, v i * p = v i) :
    ∀ i, (M *ᵥ v) i * p = (M *ᵥ v) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_mul, mul_assoc, hv]

/-- A matrix ideal supported by `diag(p,q)` has a separate support condition
on each of its two columns, hence four coefficient entries. -/
theorem matrix_diagonal_support_iff (X : BdGBlock B) (p q : B) :
    X * !![p, 0; 0, q] = X ↔
      (∀ i, X i 0 * p = X i 0) ∧ (∀ i, X i 1 * q = X i 1) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using
        congrArg (fun M : BdGBlock B => M i 0) h
    · intro i
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using
        congrArg (fun M : BdGBlock B => M i 1) h
  · rintro ⟨hp, hq⟩
    ext i j
    fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hp i
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hq i

section Metric

variable [StarRing B]

/-- The two-sheet metric over a coefficient involution; no centrality is assumed. -/
def doubledMetric (η : B) : BdGBlock B := !![η, 0; 0, -η]

theorem doubledMetric_star (η : B) (hη : star η = η) :
    star (doubledMetric η) = doubledMetric η := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [doubledMetric, Matrix.star_apply, hη]

theorem doubledMetric_sq (η : B) (hη : η * η = 1) :
    doubledMetric η * doubledMetric η = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [doubledMetric, Matrix.mul_apply, Fin.sum_univ_two, hη]

/-- Inserting the metric again cancels the metric in the column pairing. -/
theorem bilinear_involution_cancel {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n B) (hG : G * G = 1) (v w : n → B) :
    bilinear G G v w = star v ⬝ᵥ w := by
  unfold bilinear diracRow
  rw [dotProduct_mulVec, vecMul_vecMul, hG, vecMul_one]

theorem doubled_bilinear_cancel (η : B) (hη : η * η = 1) (v w : Fin 2 → B) :
    bilinear (doubledMetric η) (doubledMetric η) v w = star v ⬝ᵥ w :=
  bilinear_involution_cancel _ (doubledMetric_sq η hη) v w

/-- In an operator-ideal product the left metric factor remains. This is a
different typing from a column bra and prevents an invalid cancellation. -/
theorem sharp_metric_product (G X Y : B) (hG : G * G = 1) :
    InfoGeometry.Canonical.SpinorialCore.Krein.sharp G X * G * Y =
      G * star X * Y := by
  unfold InfoGeometry.Canonical.SpinorialCore.Krein.sharp
  calc
    _ = G * star X * (G * G) * Y := by noncomm_ring
    _ = G * star X * Y := by rw [hG, mul_one]

/-- The corrected operator-ideal Gram formula includes the second metric
on the left as well. -/
theorem metric_sharp_metric_product (G X Y : B) (hG : G * G = 1) :
    G * (InfoGeometry.Canonical.SpinorialCore.Krein.sharp G X * G * Y) =
      star X * Y := by
  rw [sharp_metric_product G X Y hG]
  simp only [← mul_assoc, hG, one_mul]

end Metric

end InfoGeometry.CliffordWeyl.RealDoubledIdealMetric
