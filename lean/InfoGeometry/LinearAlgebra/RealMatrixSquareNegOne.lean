/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.LinearAlgebra.FiniteRealAnticommutation
import InfoGeometry.Quantum.Realification
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Real matrix roots of minus the identity

A finite real matrix squares to minus the identity exactly when its index
cardinality is even. Necessity belongs to `FiniteRealAnticommutation`;
sufficiency transports the existing real `Realification.internalJ` through
a finite-index equivalence.

The native matrix-composition ring equivalence then gives the exact criterion
for matrices whose entries are real matrix blocks. Their real column-space
dimension is the product of the two index cardinalities. In particular, three
outer indices permit a root exactly when the real block size is even.

The final counterexample uses the two-dimensional real algebra `ℝ × ℝ`.
It has even real dimension but no root of minus one, and neither does its
three-by-three matrix ring. Thus the block-matrix classification does not extend
to arbitrary real coefficient algebras by dimension parity alone.
-/

namespace InfoGeometry.LinearAlgebra.RealMatrixSquareNegOne

section RealMatrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every even finite real dimension carries the existing doubled-space
complex structure, transported through a native matrix reindexing. -/
theorem exists_matrix_square_eq_neg_one_of_even
    (heven : Even (Fintype.card n)) :
    ∃ A : Matrix n n ℝ, A * A = -1 := by
  classical
  rcases heven with ⟨k, hk⟩
  let e : Fin k ⊕ Fin k ≃ n := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sum, Fintype.card_fin] using hk.symm)
  let E := Matrix.reindexRingEquiv ℝ e
  refine ⟨E (InfoGeometry.Quantum.Realification.internalJ (n := Fin k)), ?_⟩
  simpa only [map_mul, map_neg, map_one] using
    congrArg E (InfoGeometry.Quantum.Realification.internalJ_sq (n := Fin k))

/-- Real square roots of minus the identity exist in precisely the even
finite dimensions, including dimension zero. -/
theorem exists_matrix_square_eq_neg_one_iff :
    (∃ A : Matrix n n ℝ, A * A = -1) ↔ Even (Fintype.card n) := by
  constructor
  · rintro ⟨A, hA⟩
    exact FiniteRealAnticommutation.even_card_of_square_eq_neg_one hA
  · exact exists_matrix_square_eq_neg_one_of_even

end RealMatrices

section RealBlockMatrices

variable {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq m] [DecidableEq k]

/-- Flattening actual real matrix blocks gives the exact parity criterion
on the dimension of the real column space. -/
theorem exists_block_matrix_square_eq_neg_one_iff :
    (∃ A : Matrix m m (Matrix k k ℝ), A * A = -1) ↔
      Even (Fintype.card m * Fintype.card k) := by
  let e := Matrix.compRingEquiv m k ℝ
  constructor
  · rintro ⟨A, hA⟩
    have hflat : e A * e A = -1 := by
      simpa only [map_mul, map_neg, map_one] using congrArg e hA
    simpa only [Fintype.card_prod] using
      FiniteRealAnticommutation.even_card_of_square_eq_neg_one hflat
  · intro heven
    have hcard : Even (Fintype.card (m × k)) := by
      simpa only [Fintype.card_prod] using heven
    obtain ⟨A, hA⟩ := exists_matrix_square_eq_neg_one_of_even (n := m × k) hcard
    refine ⟨e.symm A, ?_⟩
    simpa only [map_mul, map_neg, map_one] using congrArg e.symm hA

/-- At outer matrix size three, the real block size must be even and this
condition is sufficient. No nonzero-size hypothesis is needed. -/
theorem exists_three_block_matrix_square_eq_neg_one_iff :
    (∃ A : Matrix (Fin 3) (Fin 3) (Matrix k k ℝ), A * A = -1) ↔
      Even (Fintype.card k) := by
  simpa only [Fintype.card_fin, Nat.even_mul,
    show ¬Even (3 : ℕ) by decide, false_or] using
      (exists_block_matrix_square_eq_neg_one_iff (m := Fin 3) (k := k))

end RealBlockMatrices

/-- The standard numerical-index form of the three-by-three block criterion. -/
theorem exists_three_fin_block_matrix_square_eq_neg_one_iff (k : ℕ) :
    (∃ A : Matrix (Fin 3) (Fin 3) (Matrix (Fin k) (Fin k) ℝ), A * A = -1) ↔
      Even k := by
  simpa only [Fintype.card_fin] using
    (exists_three_block_matrix_square_eq_neg_one_iff (k := Fin k))

section RealProductCounterexample

/-- The product algebra is two-dimensional over the reals. -/
theorem real_prod_finrank : Module.finrank ℝ (ℝ × ℝ) = 2 := by
  simp

/-- An even-dimensional real algebra need not contain a square root of
minus one: projecting `ℝ × ℝ` onto its first real factor excludes it. -/
theorem real_prod_square_ne_neg_one (j : ℝ × ℝ) : j * j ≠ -1 := by
  intro hj
  have hfst : j.1 * j.1 = (-1 : ℝ) := congrArg Prod.fst hj
  have hnonneg := mul_self_nonneg j.1
  rw [hfst] at hnonneg
  norm_num at hnonneg

/-- The coefficient projection is an actual matrix ring homomorphism, so
odd outer size remains obstructed over the product algebra `ℝ × ℝ`. -/
theorem real_prod_matrix_square_ne_neg_one_of_odd
    {n : Type*} [Fintype n] [DecidableEq n]
    (hodd : Odd (Fintype.card n)) (A : Matrix n n (ℝ × ℝ)) :
    A * A ≠ -1 := by
  intro hA
  let f : Matrix n n (ℝ × ℝ) →+* Matrix n n ℝ :=
    (RingHom.fst ℝ ℝ).mapMatrix
  have hreal : f A * f A = -1 := by
    simpa only [map_mul, map_neg, map_one] using congrArg f hA
  have heven := FiniteRealAnticommutation.even_card_of_square_eq_neg_one hreal
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- A concrete even-dimensional real algebra for which no three-by-three
matrix squares to minus the identity. -/
theorem real_prod_even_finrank_and_no_three_matrix_root :
    Even (Module.finrank ℝ (ℝ × ℝ)) ∧
      ¬∃ A : Matrix (Fin 3) (Fin 3) (ℝ × ℝ), A * A = -1 := by
  constructor
  · rw [real_prod_finrank]
    exact ⟨1, rfl⟩
  · rintro ⟨A, hA⟩
    exact real_prod_matrix_square_ne_neg_one_of_odd (by decide) A hA

end RealProductCounterexample

end InfoGeometry.LinearAlgebra.RealMatrixSquareNegOne
