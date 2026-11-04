/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DefectIteration
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.PEquiv

/-!
# The ordered algebra of a diagonal and an involutive permutation

The permutation matrix is Mathlib's `s.toPEquiv.toMatrix`; on a column
vector it acts by precomposition with `s`. Coefficients take values in an
arbitrary semiring, so diagonal matrices need not commute with each other.

For an involution, the matrices `D(a) + X * D(b)` form a native subalgebra.
The multiplication and idempotency-defect formulas keep the order of all
coefficient products. Finite defect iteration stays in this subalgebra; no
convergence, stability, or universal dense factorization is asserted.
-/

namespace InfoGeometry.Routing.InvolutiveDiagonalAlgebra

open Matrix
open InfoGeometry.Core.IdempotencyDefect

variable {I A : Type*} [Fintype I] [DecidableEq I]

section Semiring

variable [Semiring A]

/-- The coefficients are on the right of the permutation, as in the
bit-local normal form used by the intake. -/
def localOperator (s : Equiv.Perm I) (a b : I → A) : Matrix I I A :=
  diagonal a + s.toPEquiv.toMatrix * diagonal b

/-- The permutation crosses a diagonal by reindexing its coefficients.
No commutativity of coefficient values is used. -/
theorem permutation_mul_diagonal (s : Equiv.Perm I) (a : I → A) :
    s.toPEquiv.toMatrix * diagonal a =
      diagonal (a ∘ s) * s.toPEquiv.toMatrix := by
  ext i j
  by_cases hij : j = s i
  · subst j
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply]
  · simp [Matrix.mul_diagonal, Matrix.diagonal_mul, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Ne.symm hij]

/-- Involutivity turns the opposite crossing into the same reindexing. -/
theorem diagonal_mul_permutation (s : Equiv.Perm I)
    (hs : Function.Involutive s) (a : I → A) :
    diagonal a * s.toPEquiv.toMatrix =
      s.toPEquiv.toMatrix * diagonal (a ∘ s) := by
  have hcomp : (a ∘ s) ∘ s = a := by
    funext i
    exact congrArg a (hs i)
  rw [permutation_mul_diagonal, hcomp]

/-- The native permutation matrix squares to the identity. -/
theorem permutation_square (s : Equiv.Perm I) (hs : Function.Involutive s) :
    (s.toPEquiv.toMatrix : Matrix I I A) * s.toPEquiv.toMatrix = 1 := by
  rw [PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp [Matrix.submatrix_apply, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, hs i, Matrix.one_apply]

/-- Conjugation implements the coefficient involution on the diagonal
subalgebra. -/
theorem permutation_conjugate_diagonal (s : Equiv.Perm I)
    (hs : Function.Involutive s) (a : I → A) :
    s.toPEquiv.toMatrix * diagonal a * s.toPEquiv.toMatrix = diagonal (a ∘ s) := by
  rw [permutation_mul_diagonal, mul_assoc, permutation_square s hs, mul_one]

/-- Multiplication retains the crossed coefficient order, even when the
diagonal entries are themselves noncommuting operators. -/
theorem localOperator_mul (s : Equiv.Perm I) (hs : Function.Involutive s)
    (a b c d : I → A) :
    localOperator s a b * localOperator s c d =
      localOperator s (a * c + (b ∘ s) * d) ((a ∘ s) * d + b * c) := by
  unfold localOperator
  have hcross := diagonal_mul_permutation s hs a
  have hconj := permutation_conjugate_diagonal s hs b
  calc
    _ = diagonal a * diagonal c +
        (s.toPEquiv.toMatrix * diagonal b * s.toPEquiv.toMatrix) * diagonal d +
        (diagonal a * s.toPEquiv.toMatrix) * diagonal d +
        s.toPEquiv.toMatrix * (diagonal b * diagonal c) := by noncomm_ring
    _ = _ := by
      rw [hcross, hconj]
      change _ = (diagonalRingHom I A) (a * c + (b ∘ s) * d) +
        s.toPEquiv.toMatrix * (diagonalRingHom I A) ((a ∘ s) * d + b * c)
      simp only [map_add, map_mul]
      change _ = diagonal a * diagonal c + diagonal (b ∘ s) * diagonal d +
        s.toPEquiv.toMatrix * (diagonal (a ∘ s) * diagonal d + diagonal b * diagonal c)
      noncomm_ring

/-- Addition acts independently on the two ordered coefficient functions. -/
theorem localOperator_add (s : Equiv.Perm I) (a b c d : I → A) :
    localOperator s a b + localOperator s c d = localOperator s (a + c) (b + d) := by
  unfold localOperator
  change _ = (diagonalRingHom I A) (a + c) +
    s.toPEquiv.toMatrix * (diagonalRingHom I A) (b + d)
  simp only [map_add, mul_add]
  change _ = diagonal a + diagonal c +
    (s.toPEquiv.toMatrix * diagonal b + s.toPEquiv.toMatrix * diagonal d)
  ac_rfl

end Semiring

section Ring

variable [Ring A]

theorem localOperator_sub (s : Equiv.Perm I) (a b c d : I → A) :
    localOperator s a b - localOperator s c d = localOperator s (a - c) (b - d) := by
  unfold localOperator
  change _ = (diagonalRingHom I A) (a - c) +
    s.toPEquiv.toMatrix * (diagonalRingHom I A) (b - d)
  simp only [map_sub, mul_sub]
  change _ = diagonal a - diagonal c +
    (s.toPEquiv.toMatrix * diagonal b - s.toPEquiv.toMatrix * diagonal d)
  abel

/-- The commutator measures the failure of the coefficient function to be
invariant under the permutation. -/
theorem permutation_diagonal_commutator (s : Equiv.Perm I)
    (hs : Function.Involutive s) (a : I → A) :
    s.toPEquiv.toMatrix * diagonal a - diagonal a * s.toPEquiv.toMatrix =
      s.toPEquiv.toMatrix * diagonal (a - a ∘ s) := by
  rw [diagonal_mul_permutation s hs]
  change _ = s.toPEquiv.toMatrix * (diagonalRingHom I A) (a - a ∘ s)
  rw [map_sub, mul_sub]
  rfl

/-- The exact failure of idempotence is another local operator. -/
theorem defect_localOperator (s : Equiv.Perm I) (hs : Function.Involutive s)
    (a b : I → A) :
    defect (localOperator s a b) =
      localOperator s (a * a + (b ∘ s) * b - a)
        ((a ∘ s) * b + b * a - b) := by
  rw [defect, localOperator_mul s hs, localOperator_sub]

end Ring

section Subalgebra

variable (R : Type*) [CommRing R] [Ring A] [Algebra R A]

/-- The single-permutation normal forms constitute a genuine subalgebra
of the full matrix algebra, with multiplication proved above. -/
def localSubalgebra (s : Equiv.Perm I) (hs : Function.Involutive s) :
    Subalgebra R (Matrix I I A) where
  carrier := {M | ∃ a b, M = localOperator s a b}
  zero_mem' := ⟨0, 0, by simp [localOperator]⟩
  one_mem' := ⟨1, 0, by simp [localOperator]⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, localOperator_add s a b c d⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a * c + (b ∘ s) * d, (a ∘ s) * d + b * c,
      localOperator_mul s hs a b c d⟩
  algebraMap_mem' r := ⟨algebraMap R (I → A) r, 0, by
    rw [localOperator]
    have hz : diagonal (0 : I → A) = (0 : Matrix I I A) :=
      (diagonalRingHom I A).map_zero
    rw [hz, mul_zero, add_zero]
    exact Matrix.algebraMap_eq_diagonal (n := I) (α := A) r⟩

/-- Every finite iterate remains in the same structured matrix subalgebra.
This uses the existing generic defect-iteration theorem. -/
theorem iterate_defect_local (s : Equiv.Perm I) (hs : Function.Involutive s)
    (a b : I → A) (n : ℕ) :
    defect^[n] (localOperator s a b) ∈ localSubalgebra R s hs := by
  apply InfoGeometry.Core.DefectIteration.iterate_mem_subalgebra R
    (localSubalgebra R s hs) (x := localOperator s a b) (n := n)
  exact ⟨a, b, rfl⟩

end Subalgebra

end InfoGeometry.Routing.InvolutiveDiagonalAlgebra
