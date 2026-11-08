/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.MatrixDerivation
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # The sl3 plus two vector sectors of split-octonion derivations

Uses native trace-zero matrices and the existing linear derivation carrier.
All identities in this file hold over arbitrary commutative rings.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

/-- The native special-linear Lie algebra acts faithfully by Zorn derivations. -/
def sl3Derivation : LieAlgebra.SpecialLinear.sl (Fin 3) R →ₗ⁅R⁆ Derivation (R := R) where
  toFun M := matrixDerivation M.1 M.2
  map_add' M N := by
    apply Derivation.ext
    intro X
    change matrixAction (M.1 + N.1) X = add (matrixAction M.1 X) (matrixAction N.1 X)
    ext i
    all_goals try fin_cases i
    all_goals simp [matrixAction, add, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    all_goals ring
  map_smul' r M := by
    apply Derivation.ext
    intro X
    change matrixAction (r • M.1) X = smul r (matrixAction M.1 X)
    ext i
    all_goals try fin_cases i
    all_goals simp [matrixAction, smul, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    all_goals ring
  map_lie' {M N} := by
    apply Derivation.ext
    intro X
    exact (matrixAction_bracket M.1 N.1 X).symm

theorem sl3Derivation_injective : Function.Injective (sl3Derivation (R := R)) := by
  intro M N h
  apply Subtype.ext
  apply matrixAction_injective
  funext X
  exact congrArg (fun D : Derivation (R := R) => D X) h

/-- The full action, with no hidden division or characteristic hypothesis. -/
def splitDerivation (M : LieAlgebra.SpecialLinear.sl (Fin 3) R)
    (p q : ZornVec3 R) : Derivation (R := R) :=
  sl3Derivation M + offDiagonalDerivation p q

@[simp] theorem splitDerivation_apply (M : LieAlgebra.SpecialLinear.sl (Fin 3) R)
    (p q : ZornVec3 R) (X : ZornVectorMatrix R) :
    splitDerivation M p q X = add (matrixAction M.1 X) (offDiagonalAction p q X) := rfl

/-- Upper/lower commutators land in the traceless matrix sector. -/
def mixedMatrix (p q : ZornVec3 R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => 3 * p i * q j - if i = j then ZornVec3.dot p q else 0

@[simp] theorem trace_mixedMatrix (p q : ZornVec3 R) :
    Matrix.trace (mixedMatrix p q) = 0 := by
  simp [mixedMatrix, Matrix.trace, Matrix.diag, ZornVec3.dot, Fin.sum_univ_three]
  ring

theorem offDiagonalAction_mixed_bracket (p q : ZornVec3 R) (X : ZornVectorMatrix R) :
    sub (offDiagonalAction p 0 (offDiagonalAction 0 q X))
      (offDiagonalAction 0 q (offDiagonalAction p 0 X)) =
        matrixAction (mixedMatrix p q) X := by
  ext i
  all_goals try fin_cases i
  all_goals simp [offDiagonalAction, matrixAction, mixedMatrix, sub, add, neg,
    Matrix.mulVec, dotProduct, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  all_goals ring

/-- The split norm has vanishing linear variation along every explicit derivation. -/
theorem norm_add_smul_splitDerivation
    (M : LieAlgebra.SpecialLinear.sl (Fin 3) R) (p q : ZornVec3 R)
    (t : R) (X : ZornVectorMatrix R) :
    norm (add X (smul t (splitDerivation M p q X))) =
      norm X + t ^ 2 * norm (splitDerivation M p q X) := by
  simp [splitDerivation_apply, norm, add, smul, matrixAction, offDiagonalAction,
    Matrix.mulVec, dotProduct, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  ring

/-- Polarizing the norm yields the precise skew-symmetry identity. -/
theorem splitDerivation_norm_skew
    (M : LieAlgebra.SpecialLinear.sl (Fin 3) R) (p q : ZornVec3 R)
    (X Y : ZornVectorMatrix R) :
    QuadraticMap.polar norm (splitDerivation M p q X) Y +
      QuadraticMap.polar norm X (splitDerivation M p q Y) = 0 := by
  change norm (add (splitDerivation M p q X) Y) - norm (splitDerivation M p q X) - norm Y +
    (norm (add X (splitDerivation M p q Y)) - norm X - norm (splitDerivation M p q Y)) = 0
  simp [splitDerivation_apply, norm, add, matrixAction, offDiagonalAction,
    Matrix.mulVec, dotProduct, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  ring

@[simp] theorem trace_splitDerivation (M : LieAlgebra.SpecialLinear.sl (Fin 3) R)
    (p q : ZornVec3 R) (X : ZornVectorMatrix R) :
    trace (splitDerivation M p q X) = 0 := by
  simp [splitDerivation_apply, trace, add, matrixAction, offDiagonalAction]

/-- The first Peirce idempotent recovers the two off-diagonal parameters. -/
@[simp] theorem splitDerivation_E11 (M : LieAlgebra.SpecialLinear.sl (Fin 3) R)
    (p q : ZornVec3 R) : splitDerivation M p q E11 = offDiagonal (-p) q := by
  ext i <;> simp [splitDerivation_apply, matrixAction, offDiagonalAction,
    offDiagonal, add, E11, Matrix.mulVec, dotProduct, ZornVec3.dot, ZornVec3.cross]

/-- No nonzero parameter combination is a zero derivation, even in bad characteristic. -/
theorem splitDerivation_injective : Function.Injective
    (fun t : LieAlgebra.SpecialLinear.sl (Fin 3) R × ZornVec3 R × ZornVec3 R =>
      splitDerivation t.1 t.2.1 t.2.2) := by
  rintro ⟨M, p, q⟩ ⟨N, r, s⟩ h
  have he := congrArg (fun D : Derivation (R := R) => D E11) h
  rw [splitDerivation_E11, splitDerivation_E11] at he
  have hp : p = r := by
    have hv := congrArg ZornVectorMatrix.v he
    change -p = -r at hv
    exact neg_injective hv
  have hq : q = s := congrArg ZornVectorMatrix.w he
  subst r
  subst s
  have hm : M = N := by
    apply sl3Derivation_injective
    exact add_right_cancel h
  subst N
  rfl

/-- Linearity in the two off-diagonal parameter vectors. -/
def offDiagonalParameterMap : (ZornVec3 R × ZornVec3 R) →ₗ[R] Derivation (R := R) where
  toFun pq := offDiagonalDerivation pq.1 pq.2
  map_add' pq rs := by
    apply Derivation.ext
    intro X
    change offDiagonalAction (pq.1 + rs.1) (pq.2 + rs.2) X =
      add (offDiagonalAction pq.1 pq.2 X) (offDiagonalAction rs.1 rs.2 X)
    ext i
    all_goals try fin_cases i
    all_goals simp [offDiagonalAction, add, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    all_goals ring
  map_smul' r pq := by
    apply Derivation.ext
    intro X
    change offDiagonalAction (r • pq.1) (r • pq.2) X = smul r (offDiagonalAction pq.1 pq.2 X)
    ext i
    all_goals try fin_cases i
    all_goals simp [offDiagonalAction, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    all_goals ring

/-- The native linear map from the sl3 plus two vector parameter space. -/
def splitParameterMap :
    (LieAlgebra.SpecialLinear.sl (Fin 3) R × ZornVec3 R × ZornVec3 R) →ₗ[R]
      Derivation (R := R) :=
  sl3Derivation.toLinearMap.comp (LinearMap.fst _ _ _) +
    offDiagonalParameterMap.comp (LinearMap.snd _ _ _)

@[simp] theorem splitParameterMap_apply
    (t : LieAlgebra.SpecialLinear.sl (Fin 3) R × ZornVec3 R × ZornVec3 R) :
    splitParameterMap t = splitDerivation t.1 t.2.1 t.2.2 := rfl

/-- Matrix coordinate of the full derivation bracket. -/
def splitBracketMatrix (M N : LieAlgebra.SpecialLinear.sl (Fin 3) R)
    (p q r s : ZornVec3 R) : LieAlgebra.SpecialLinear.sl (Fin 3) R :=
  ⟨M.1 * N.1 - N.1 * M.1 + mixedMatrix p s - mixedMatrix r q, by
    change Matrix.trace (M.1 * N.1 - N.1 * M.1 + mixedMatrix p s - mixedMatrix r q) = 0
    rw [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sub,
      trace_mixedMatrix, trace_mixedMatrix, Matrix.trace_mul_comm M.1 N.1]
    ring⟩

set_option maxHeartbeats 2000000 in
/-- All fourteen bracket coordinates, preserving the multiplication order. -/
theorem splitDerivation_bracket (M N : LieAlgebra.SpecialLinear.sl (Fin 3) R)
    (p q r s : ZornVec3 R) :
    ⁅splitDerivation M p q, splitDerivation N r s⁆ =
      splitDerivation (splitBracketMatrix M N p q r s)
        (M.1.mulVec r - N.1.mulVec p - 2 • ZornVec3.cross q s)
        (-M.1.transpose.mulVec s + N.1.transpose.mulVec q + 2 • ZornVec3.cross p r) := by
  have hM : M.1 2 2 = -M.1 0 0 - M.1 1 1 := by
    have h := M.2
    change Matrix.trace M.1 = 0 at h
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three] at h
    linear_combination h
  have hN : N.1 2 2 = -N.1 0 0 - N.1 1 1 := by
    have h := N.2
    change Matrix.trace N.1 = 0 at h
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three] at h
    linear_combination h
  apply Derivation.ext
  intro X
  change sub (splitDerivation M p q (splitDerivation N r s X))
    (splitDerivation N r s (splitDerivation M p q X)) = _
  simp only [splitDerivation_apply]
  ext i
  all_goals try fin_cases i
  all_goals simp [splitBracketMatrix, matrixAction, offDiagonalAction, mixedMatrix,
    sub, add, neg, Matrix.mulVec, Matrix.mul_apply, dotProduct, ZornVec3.dot,
    ZornVec3.cross, Fin.sum_univ_three, hM, hN, two_smul]
  all_goals ring

end InfoGeometry.Algebra.ZornVectorMatrix
