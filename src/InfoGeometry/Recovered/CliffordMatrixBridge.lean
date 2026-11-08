/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import InfoGeometry.Recovered.SplitQuaternionMatricesRecovered

/-!
# Cl(1,1) matrix bridge — statement surface

The earlier recovered file attempted to construct the full Clifford algebra lift
using an unproved metric-closure lemma.  This replacement keeps the concrete
linear map and exposes the universal-property obligation as an explicit
proposition.  No algebra homomorphism is installed until that obligation is
proved.
-/

namespace InfoGeometry.Recovered.CliffordMatrixBridge

open Matrix
open InfoGeometry.SplitQuaternion

noncomputable section

/-- The quadratic form with signature `(1,1)` on `Fin 2 → ℚ`. -/
def q11 : QuadraticForm ℚ (Fin 2 → ℚ) := QuadraticMap.proj 0 0 - QuadraticMap.proj 1 1

/-- The concrete function sending the positive generator to `splitJ` and the
negative generator to `splitI`.  Linearity is not packaged here. -/
def cl11ToMatrix (v : Fin 2 → ℚ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (v 0 : ℝ) • splitJ + (v 1 : ℝ) • splitI

/-- The concrete matrix representation satisfies the `(1,1)` Clifford
quadratic relation.  This is the metric-closure theorem needed before using
the universal property of `CliffordAlgebra` to construct the induced map. -/
theorem cl11ToMatrix_sq_statement :
    ∀ v : Fin 2 → ℚ,
      cl11ToMatrix v * cl11ToMatrix v =
        algebraMap ℚ (Matrix (Fin 2) (Fin 2) ℝ) (q11 v) := by
  intro v
  have hcross : splitJ * splitI + splitI * splitJ = 0 :=
    splitJ_splitI_anticommutator_zero
  have hrhs :
      algebraMap ℚ (Matrix (Fin 2) (Fin 2) ℝ) (q11 v) =
        ((v 0 : ℝ) ^ 2 - (v 1 : ℝ) ^ 2) • splitOne := by
    ext i j
    rw [Matrix.algebraMap_matrix_apply]
    fin_cases i <;> fin_cases j <;>
      simp [q11, splitOne, QuadraticMap.proj_apply, Matrix.smul_apply] <;>
        ring
  rw [hrhs]
  let a : ℝ := v 0
  let b : ℝ := v 1
  have hcross_smul :
      a • (b • (splitI * splitJ)) +
          b • (a • (splitJ * splitI)) = 0 := by
    calc
      a • (b • (splitI * splitJ)) + b • (a • (splitJ * splitI)) =
          (a * b) • (splitI * splitJ + splitJ * splitI) := by
            rw [smul_smul, smul_smul, mul_comm b a, ← smul_add]
      _ = 0 := by
        rw [add_comm, hcross, smul_zero]
  have hcross' :
      (a * b) • (splitI * splitJ) +
          (b * a) • (splitJ * splitI) = 0 := by
    simpa only [smul_smul] using hcross_smul
  have hdiag' :
      (a * a) • splitOne + (b * b) • (-splitOne) =
        (a ^ 2 - b ^ 2) • splitOne := by
    rw [pow_two, pow_two]
    module
  change (a • splitJ + b • splitI) * (a • splitJ + b • splitI) =
    (a ^ 2 - b ^ 2) • splitOne
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_smul, smul_add, splitJ_sq, splitI_sq]
  calc
    _ = ((a * a) • splitOne + (b * b) • (-splitOne)) +
          ((a * b) • (splitI * splitJ) +
            (b * a) • (splitJ * splitI)) := by abel
    _ = (a ^ 2 - b ^ 2) • splitOne := by
      rw [hdiag', hcross', add_zero]

end

end InfoGeometry.Recovered.CliffordMatrixBridge
