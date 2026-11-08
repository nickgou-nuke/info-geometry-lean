/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.OffDiagonalDerivation
import InfoGeometry.OperatorAlgebra.MatrixThreeAdjugate
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Traceless matrix derivations of the existing Zorn algebra

The matrix acts on the upper vector and its negative transpose on the lower
vector. The Leibniz condition is exactly trace zero, over any commutative ring.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

/-- Infinitesimal covariance of the three-dimensional cross product. -/
theorem mulVec_cross_trace (M : Matrix (Fin 3) (Fin 3) R) (u v : ZornVec3 R) :
    ZornVec3.cross (M.mulVec u) v + ZornVec3.cross u (M.mulVec v) +
      M.transpose.mulVec (ZornVec3.cross u v) =
        Matrix.trace M • ZornVec3.cross u v := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Matrix.trace, Matrix.diag,
      ZornVec3.cross, Fin.sum_univ_three] <;> ring

/-- Matrix action before imposing the Leibniz condition. -/
def matrixAction (M : Matrix (Fin 3) (Fin 3) R) (X : ZornVectorMatrix R) :
    ZornVectorMatrix R :=
  ⟨0, M.mulVec X.v, -M.transpose.mulVec X.w, 0⟩

theorem matrixAction_leibniz (M : Matrix (Fin 3) (Fin 3) R)
    (hM : Matrix.trace M = 0) (X Y : ZornVectorMatrix R) :
    matrixAction M (mul X Y) =
      add (mul (matrixAction M X) Y) (mul X (matrixAction M Y)) := by
  have h22 : M 2 2 = -M 0 0 - M 1 1 := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three] at hM
    linear_combination hM
  ext i
  all_goals try fin_cases i
  all_goals simp [matrixAction, mul, add, Matrix.mulVec, dotProduct,
    ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three, h22]
  all_goals ring

theorem matrixAction_leibniz_iff (M : Matrix (Fin 3) (Fin 3) R) :
    (∀ X Y, matrixAction M (mul X Y) =
      add (mul (matrixAction M X) Y) (mul X (matrixAction M Y))) ↔
        Matrix.trace M = 0 := by
  constructor
  · intro h
    have hw := congrArg (fun X : ZornVectorMatrix R => X.w 2) (h (U 0) (U 1))
    simp [matrixAction, mul, add, U, ZornVec3.basis, Matrix.mulVec,
      dotProduct, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] at hw
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three]
    linear_combination -hw
  · exact matrixAction_leibniz M

/-- The actual linear derivation associated with a traceless matrix. -/
def matrixDerivation (M : Matrix (Fin 3) (Fin 3) R) (hM : Matrix.trace M = 0) :
    Derivation (R := R) where
  toFun := matrixAction M
  map_add' X Y := by
    ext i
    all_goals try fin_cases i
    all_goals simp [matrixAction, add, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    all_goals ring
  map_smul' r X := by
    ext i
    all_goals try fin_cases i
    all_goals simp [matrixAction, smul, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    all_goals ring
  map_mul' := matrixAction_leibniz M hM

@[simp] theorem matrixAction_E11 (M : Matrix (Fin 3) (Fin 3) R) :
    matrixAction M E11 = zero := by
  ext i <;> simp [matrixAction, E11, zero, Matrix.mulVec, dotProduct]

@[simp] theorem matrixAction_E22 (M : Matrix (Fin 3) (Fin 3) R) :
    matrixAction M E22 = zero := by
  ext i <;> simp [matrixAction, E22, zero, Matrix.mulVec, dotProduct]

@[simp] theorem trace_matrixAction (M : Matrix (Fin 3) (Fin 3) R)
    (X : ZornVectorMatrix R) : trace (matrixAction M X) = 0 := by
  simp [trace, matrixAction]

/-- Faithfulness is visible on the upper basis vectors, in every characteristic. -/
theorem matrixAction_injective :
    Function.Injective (matrixAction (R := R)) := by
  intro M N h
  ext i j
  have hv := congrArg (fun f => (f (U j)).v i) h
  simpa [matrixAction, U, Matrix.mulVec, dotProduct, ZornVec3.basis] using hv

/-- Commutators intertwine without a trace hypothesis on the input matrices. -/
theorem matrixAction_bracket (M N : Matrix (Fin 3) (Fin 3) R)
    (X : ZornVectorMatrix R) :
    sub (matrixAction M (matrixAction N X)) (matrixAction N (matrixAction M X)) =
      matrixAction (M * N - N * M) X := by
  ext i
  all_goals try fin_cases i
  all_goals simp [matrixAction, sub, add, neg, Matrix.mulVec,
    Matrix.mul_apply, dotProduct, Fin.sum_univ_three]
  all_goals ring

/-- Mixed matrix/off-diagonal bracket: the two vector representations are dual. -/
theorem matrixAction_offDiagonal_bracket (M : Matrix (Fin 3) (Fin 3) R)
    (hM : Matrix.trace M = 0) (p q : ZornVec3 R) (X : ZornVectorMatrix R) :
    sub (matrixAction M (offDiagonalAction p q X))
      (offDiagonalAction p q (matrixAction M X)) =
        offDiagonalAction (M.mulVec p) (-M.transpose.mulVec q) X := by
  have h22 : M 2 2 = -M 0 0 - M 1 1 := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three] at hM
    linear_combination hM
  ext i
  all_goals try fin_cases i
  all_goals simp [matrixAction, offDiagonalAction, sub, add, neg,
    Matrix.mulVec, dotProduct, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three, h22]
  all_goals ring

end InfoGeometry.Algebra.ZornVectorMatrix
