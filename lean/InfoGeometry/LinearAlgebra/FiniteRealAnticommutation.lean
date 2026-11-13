/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum

/-!
# Finite real anticommutation and dimension parity

Two invertible anticommuting real endomorphisms require even dimension.
Neither endomorphism is assumed involutive. In odd dimension an invertible
reversing map therefore forces the reversed endomorphism to be singular.

The matrix products retain their order. Commutativity is used only after
applying the real determinant. The dimension is the dimension of the real
representation space, not an external matrix index over a coefficient algebra.
-/

namespace InfoGeometry.LinearAlgebra.FiniteRealAnticommutation

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Taking determinants retains the parity sign in an anticommutation law. -/
theorem det_product_eq_sign_mul {A B : Matrix n n ℝ}
    (hAB : A * B = -(B * A)) :
    A.det * B.det = (-1 : ℝ) ^ Fintype.card n * (A.det * B.det) := by
  calc
    A.det * B.det = (A * B).det := (Matrix.det_mul A B).symm
    _ = (-(B * A)).det := congrArg Matrix.det hAB
    _ = (-1 : ℝ) ^ Fintype.card n * (B.det * A.det) := by
      rw [Matrix.det_neg, Matrix.det_mul]
    _ = (-1 : ℝ) ^ Fintype.card n * (A.det * B.det) := by
      rw [mul_comm B.det A.det]

/-- In odd real dimension, the product of the two determinants vanishes. -/
theorem det_product_eq_zero_of_odd {A B : Matrix n n ℝ}
    (hAB : A * B = -(B * A)) (hodd : Odd (Fintype.card n)) :
    A.det * B.det = 0 := by
  have hsign := det_product_eq_sign_mul hAB
  rw [hodd.neg_one_pow, neg_one_mul] at hsign
  exact CharZero.eq_neg_self_iff.mp hsign

/-- Nonzero determinants of an anticommuting real pair force even dimension. -/
theorem even_card_of_det_ne_zero {A B : Matrix n n ℝ}
    (hAB : A * B = -(B * A)) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    Even (Fintype.card n) := by
  rcases Nat.even_or_odd (Fintype.card n) with heven | hodd
  · exact heven
  · exact False.elim ((mul_ne_zero hA hB) (det_product_eq_zero_of_odd hAB hodd))

/-- The invertible-pair obstruction needs no square or involutivity hypotheses. -/
theorem even_card_of_isUnit {A B : Matrix n n ℝ}
    (hAB : A * B = -(B * A)) (hA : IsUnit A) (hB : IsUnit B) :
    Even (Fintype.card n) :=
  even_card_of_det_ne_zero hAB
    ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero
    ((Matrix.isUnit_iff_isUnit_det B).mp hB).ne_zero

/-- An invertible reversing matrix in odd dimension forces a zero determinant. -/
theorem det_eq_zero_of_odd_of_isUnit {A B : Matrix n n ℝ}
    (hAB : A * B = -(B * A)) (hodd : Odd (Fintype.card n)) (hA : IsUnit A) :
    B.det = 0 := by
  have hA0 : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero
  exact (mul_eq_zero.mp (det_product_eq_zero_of_odd hAB hodd)).resolve_left hA0

/-- The same obstruction stated using the native ring-unit predicate. -/
theorem not_isUnit_of_odd_of_isUnit {A B : Matrix n n ℝ}
    (hAB : A * B = -(B * A)) (hodd : Odd (Fintype.card n)) (hA : IsUnit A) :
    ¬IsUnit B := by
  intro hB
  exact ((Matrix.isUnit_iff_isUnit_det B).mp hB).ne_zero
    (det_eq_zero_of_odd_of_isUnit hAB hodd hA)

/-- A real square root of minus the identity also requires even dimension. -/
theorem even_card_of_square_eq_neg_one {J : Matrix n n ℝ}
    (hJ : J * J = -1) : Even (Fintype.card n) := by
  rcases Nat.even_or_odd (Fintype.card n) with heven | hodd
  · exact heven
  · have hdet : J.det * J.det = (-1 : ℝ) := by
      calc
        J.det * J.det = (J * J).det := (Matrix.det_mul J J).symm
        _ = (-(1 : Matrix n n ℝ)).det := congrArg Matrix.det hJ
        _ = -1 := by rw [Matrix.det_neg, hodd.neg_one_pow, Matrix.det_one, mul_one]
    have hnonneg := mul_self_nonneg J.det
    rw [hdet] at hnonneg
    norm_num at hnonneg

end Matrices

section Endomorphisms

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The matrix obstruction is basis-independent on every finite real vector space. -/
theorem even_finrank_of_isUnit {f g : Module.End ℝ V}
    (hfg : f * g = -(g * f)) (hf : IsUnit f) (hg : IsUnit g) :
    Even (Module.finrank ℝ V) := by
  classical
  let e := LinearMap.toMatrixAlgEquiv (Module.finBasis ℝ V)
  have hmatrix : e f * e g = -(e g * e f) := by
    simpa only [map_mul, map_neg] using congrArg e hfg
  simpa only [Fintype.card_fin] using
    even_card_of_isUnit hmatrix
      (IsUnit.map e hf) (IsUnit.map e hg)

/-- An invertible reversing endomorphism forces singularity in odd dimension. -/
theorem not_isUnit_of_odd_finrank {f g : Module.End ℝ V}
    (hfg : f * g = -(g * f)) (hodd : Odd (Module.finrank ℝ V)) (hf : IsUnit f) :
    ¬IsUnit g := by
  intro hg
  exact (Nat.not_even_iff_odd.mpr hodd) (even_finrank_of_isUnit hfg hf hg)

/-- The square-root obstruction also transports to arbitrary finite real modules. -/
theorem even_finrank_of_square_eq_neg_one {J : Module.End ℝ V}
    (hJ : J * J = -1) : Even (Module.finrank ℝ V) := by
  classical
  let e := LinearMap.toMatrixAlgEquiv (Module.finBasis ℝ V)
  have hmatrix : e J * e J = -1 := by
    simpa only [map_mul, map_neg, map_one] using congrArg e hJ
  simpa only [Fintype.card_fin] using even_card_of_square_eq_neg_one hmatrix

end Endomorphisms

end InfoGeometry.LinearAlgebra.FiniteRealAnticommutation
