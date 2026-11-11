/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateModularShiftGeometry
import InfoGeometry.OperatorAlgebra.LieJordanEndomorphisms
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Invertible
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Native matrix transport of the Peirce Hadamard identity

The source carrier is the existing
`NonCommutativeTwoStateAndModularShift.Mat2 R`, with its ordered matrix
multiplication over an arbitrary `[Ring R]`. The target is Mathlib's native
`Matrix (Fin 2) (Fin 2) R`. The explicit `RingEquiv` transports the existing
Walsh identity; specializing the coefficient ring to `Module.End ℤ R` gives
the existing unnormalized Jordan and Lie multiplication operators.

The unnormalized identity holds in every characteristic. A genuine similarity
uses the explicit inverse supplied only under `[Invertible (2 : R)]`.
No definition or interpretation of the intake symbol `θΩ` is asserted.

Validation status and interpretation limits are recorded in
`docs/TWISTOR_INVARIANTS_HADAMARD_CONTRACT.md`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceHadamardNative

open NonCommutativeTwoStateAndModularShift (Mat2)
open NonCommutativeTwoStateAndModularShift.Mat2
  (H_Walsh localObs diagScalar modularShift
    archetype_R1_walsh_hadamard_localization_shift_duality)

variable {R : Type*} [Ring R]

/-- The existing four-entry ring and native two-by-two matrices have the same
ordered multiplication, over every possibly noncommutative coefficient ring. -/
def mat2EquivMatrix : Mat2 R ≃+* Matrix (Fin 2) (Fin 2) R where
  toFun M := !![M.a11, M.a12; M.a21, M.a22]
  invFun M := ⟨M 0 0, M 0 1, M 1 0, M 1 1⟩
  left_inv M := by
    cases M
    rfl
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  map_add' M N := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- The native matrix is the image of the existing Peirce Walsh element. -/
def walsh : Matrix (Fin 2) (Fin 2) R :=
  mat2EquivMatrix (H_Walsh : Mat2 R)

theorem walsh_eq : walsh (R := R) = !![1, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [walsh, mat2EquivMatrix, H_Walsh,
      NonCommutativeTwoStateAndModularShift.Mat2.Ex,
      NonCommutativeTwoStateAndModularShift.Mat2.Ez]

/-- Transport of the source identity, including its factor of two. -/
theorem walsh_square : walsh (R := R) * walsh = 1 + 1 := by
  have h := congrArg (mat2EquivMatrix (R := R))
    (archetype_R1_walsh_hadamard_localization_shift_duality (0 : R) 0).1
  simpa only [walsh, map_mul, map_add, map_one] using h

/-- The existing arbitrary-ring Walsh theorem, transported to native matrices.
The two coefficients need not commute. -/
theorem walsh_diagonal (a b : R) :
    walsh * !![a, 0; 0, b] * walsh =
      !![a + b, a - b; a - b, a + b] := by
  calc
    walsh * !![a, 0; 0, b] * walsh =
        mat2EquivMatrix (H_Walsh * localObs a b * H_Walsh) := by
      rw [map_mul, map_mul]
      rfl
    _ = mat2EquivMatrix
        (diagScalar (a + b) + modularShift (a - b) (a - b)) :=
      congrArg mat2EquivMatrix
        (archetype_R1_walsh_hadamard_localization_shift_duality a b).2.2.2.2
    _ = !![a + b, a - b; a - b, a + b] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [mat2EquivMatrix, diagScalar, modularShift]

/-- The complete native-matrix transform, including both off-diagonal entries.
No commutation between the four entries is assumed. -/
theorem walsh_matrix (M : Matrix (Fin 2) (Fin 2) R) :
    walsh * M * walsh =
      !![(M 0 0 + M 0 1) + (M 1 0 + M 1 1),
         (M 0 0 - M 0 1) + (M 1 0 - M 1 1);
         (M 0 0 + M 0 1) - (M 1 0 + M 1 1),
         (M 0 0 - M 0 1) - (M 1 0 - M 1 1)] := by
  simp only [walsh_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> abel

/-- The Walsh matrix becomes a unit when two is invertible. Its inverse keeps
the order of all coefficient products explicit. -/
def walshUnit [Invertible (2 : R)] : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := walsh
  inv := !![⅟ (2 : R), ⅟ (2 : R); ⅟ (2 : R), -⅟ (2 : R)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [walsh_eq, Matrix.mul_apply, Fin.sum_univ_two,
        invOf_two_add_invOf_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [walsh_eq, Matrix.mul_apply, Fin.sum_univ_two,
        invOf_two_add_invOf_two]

/-- Actual native-matrix similarity. The inverse of two is placed on the
right explicitly, without any commutativity assumption on `R`. -/
theorem walshUnit_similarity [Invertible (2 : R)]
    (M : Matrix (Fin 2) (Fin 2) R) :
    (walshUnit : (Matrix (Fin 2) (Fin 2) R)ˣ).val *
        M * (walshUnit⁻¹).val =
      !![((M 0 0 + M 0 1) + (M 1 0 + M 1 1)) * ⅟ (2 : R),
         ((M 0 0 - M 0 1) + (M 1 0 - M 1 1)) * ⅟ (2 : R);
         ((M 0 0 + M 0 1) - (M 1 0 + M 1 1)) * ⅟ (2 : R),
         ((M 0 0 - M 0 1) - (M 1 0 - M 1 1)) * ⅟ (2 : R)] := by
  have hInv :
      ((walshUnit (R := R))⁻¹).val =
        walsh * !![⅟ (2 : R), 0; 0, ⅟ (2 : R)] := by
    change !![⅟ (2 : R), ⅟ (2 : R); ⅟ (2 : R), -⅟ (2 : R)] = _
    rw [walsh_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  change walsh * M * ((walshUnit (R := R))⁻¹).val = _
  rw [hInv, ← mul_assoc, walsh_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- For every associative ring, the native left/right multiplication block
transforms to the repository's existing unnormalized Jordan/Lie operators. -/
theorem walsh_leftRight (J : R) :
    walsh * !![LinearMap.mulLeft ℤ J, 0; 0, LinearMap.mulRight ℤ J] * walsh =
      !![LieJordan.jordanOp ℤ J, LieJordan.lieOp ℤ J;
         LieJordan.lieOp ℤ J, LieJordan.jordanOp ℤ J] := by
  simpa only [LieJordan.jordanOp, LieJordan.lieOp] using
    (walsh_diagonal (LinearMap.mulLeft ℤ J) (LinearMap.mulRight ℤ J))

end InfoGeometry.OperatorAlgebra.PeirceHadamardNative
