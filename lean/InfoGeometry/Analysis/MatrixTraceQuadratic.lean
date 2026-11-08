/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.ComplexMatrixLogDetCalculus
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # The real trace pairing and its native quadratic differential

The domain is the full complex matrix algebra with its operator norm.
The trace pairing is real bilinear and positive definite. Its value is not
the operator norm squared; no identification of those two norms is made.
-/

noncomputable section

namespace InfoGeometry.Analysis.MatrixTraceQuadratic

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
open ComplexMatrixLogDetCalculus

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- The real Hilbert--Schmidt pairing, expressed through ordered multiplication. -/
def tracePair : Mat →L[ℝ] Mat →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ Mat Mat ℝ realTraceCLM).comp
    (ContinuousLinearMap.mul ℝ Mat)).comp (starL' ℝ).toContinuousLinearMap

@[simp] theorem tracePair_apply (X Y : Mat) :
    tracePair X Y = (Matrix.trace (star X * Y)).re := rfl

theorem tracePair_comm (X Y : Mat) : tracePair X Y = tracePair Y X := by
  change (Matrix.trace (Xᴴ * Y)).re = (Matrix.trace (Yᴴ * X)).re
  have h := congrArg Complex.re (Matrix.trace_conjTranspose (Xᴴ * Y))
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Complex.star_def, Complex.conj_re] using h.symm

theorem tracePair_self_nonneg (X : Mat) : 0 ≤ tracePair X X := by
  exact (Complex.nonneg_iff.mp
    (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).1

theorem tracePair_self_eq_zero_iff (X : Mat) : tracePair X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    apply Complex.ext
    · exact h
    · exact (Complex.nonneg_iff.mp
        (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).2.symm
  · rintro rfl
    simp

theorem tracePair_self_pos_iff (X : Mat) : 0 < tracePair X X ↔ X ≠ 0 := by
  constructor
  · intro h hX
    exact h.ne' ((tracePair_self_eq_zero_iff X).mpr hX)
  · intro hX
    exact lt_of_le_of_ne (tracePair_self_nonneg X)
      (Ne.symm (mt (tracePair_self_eq_zero_iff X).mp hX))

/-- Half the positive trace square. -/
def halfTraceSquare (X : Mat) : ℝ := (1 / 2 : ℝ) * tracePair X X

theorem hasFDerivAt_halfTraceSquare (X : Mat) :
    HasFDerivAt halfTraceSquare (tracePair X) X := by
  have h := (tracePair.hasFDerivAt_of_bilinear
    (hasFDerivAt_id X) (hasFDerivAt_id X)).const_mul (1 / 2 : ℝ)
  convert! h using 1
  ext Y
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, id_eq, smul_eq_mul]
  rw [tracePair_comm Y X]
  ring

@[simp] theorem fderiv_halfTraceSquare (X : Mat) :
    fderiv ℝ halfTraceSquare X = tracePair X :=
  (hasFDerivAt_halfTraceSquare X).fderiv

/-- The original negative trace-square convention is positive on skew-adjoint inputs. -/
theorem tracePair_self_of_star_eq_neg (X : Mat) (hX : star X = -X) :
    tracePair X X = -(Matrix.trace (X * X)).re := by
  simp [tracePair_apply, hX, neg_mul]

/-- Unitary conjugation preserves the pairing on all matrix inputs. -/
theorem tracePair_unitary_conjugate (U : unitary Mat) (X Y : Mat) :
    tracePair ((U : Mat) * X * star (U : Mat))
      ((U : Mat) * Y * star (U : Mat)) = tracePair X Y := by
  have hmul :
      star ((U : Mat) * X * star (U : Mat)) *
        ((U : Mat) * Y * star (U : Mat)) =
          (U : Mat) * (star X * Y) * star (U : Mat) := by
    simp only [star_mul, star_star]
    calc
      _ = (U : Mat) * star X * (star (U : Mat) * (U : Mat)) * Y *
          star (U : Mat) := by noncomm_ring
      _ = _ := by simp [mul_assoc]
  rw [tracePair_apply, hmul, Matrix.trace_mul_cycle]
  simp [tracePair_apply]

end InfoGeometry.Analysis.MatrixTraceQuadratic
