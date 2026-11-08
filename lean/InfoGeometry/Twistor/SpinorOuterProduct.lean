import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace InfoGeometry.Twistor.SpinorOuterProduct

open Matrix

section CommutativeRing

variable {Scalar Index : Type*} [CommRing Scalar]

theorem bilinear_scaling (scalar : Scalar) (left right : Index → Scalar) :
    vecMulVec (scalar • left) (scalar • right) =
      scalar ^ 2 • vecMulVec left right := by
  rw [smul_vecMulVec, vecMulVec_smul, smul_smul, ← pow_two]

variable [StarRing Scalar]

theorem hermitian_outer_scaling (leftScalar rightScalar : Scalar)
    (left right : Index → Scalar) :
    vecMulVec (leftScalar • left) (star (rightScalar • right)) =
      (leftScalar * star rightScalar) • vecMulVec left (star right) := by
  ext row column
  simp [vecMulVec, smul_eq_mul, StarMul.star_mul]
  ring

theorem outer_phase_invariant (scalar : Scalar)
    (unitPhase : scalar * star scalar = 1) (left right : Index → Scalar) :
    vecMulVec (scalar • left) (star (scalar • right)) =
      vecMulVec left (star right) := by
  rw [hermitian_outer_scaling, unitPhase, one_smul]

theorem det_sum_self_outer (left right : Fin 2 → Scalar) :
    (vecMulVec left (star left) + vecMulVec right (star right)).det =
      (left 0 * right 1 - left 1 * right 0) *
        star (left 0 * right 1 - left 1 * right 0) := by
  simp [Matrix.det_fin_two, vecMulVec, star_sub, StarMul.star_mul]
  ring

theorem det_sum_self_outer_eq_zero_iff [IsDomain Scalar]
    (left right : Fin 2 → Scalar) :
    (vecMulVec left (star left) + vecMulVec right (star right)).det = 0 ↔
      left 0 * right 1 = left 1 * right 0 := by
  rw [det_sum_self_outer]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hdet | hstar
    · exact sub_eq_zero.mp hdet
    · have hminor : left 0 * right 1 - left 1 * right 0 = 0 := by
        have h := congrArg star hstar
        simpa using h
      exact sub_eq_zero.mp hminor
  · intro h
    rw [sub_eq_zero.mpr h, star_zero, mul_zero]

end CommutativeRing

theorem complex_outer_scaling (scalar : ℂ) (spinor : Fin 2 → ℂ) :
    vecMulVec (scalar • spinor) (star (scalar • spinor)) =
      (Complex.normSq scalar : ℂ) • vecMulVec spinor (star spinor) := by
  rw [hermitian_outer_scaling]
  congr 1
  exact Complex.mul_conj scalar

end InfoGeometry.Twistor.SpinorOuterProduct
