import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge

/-!
# 24-dimensional nested realization of the cyclotomic stage matrices

The concrete stage owner supplies exact standard-basis matrices for the
tripotent, complex, `Phi6`, `Phi8`, `Phi12`, and `Phi24` sectors.  Their
respective dimensions are

`3 + 3 + 2 + 4 + 4 + 8 = 24`.

This file places those matrices on one direct-sum carrier and proves that the
resulting block operator satisfies the common master equation `T^25 = T`.

The construction is purely algebraic.  The direct-sum blocks are not asserted
to be a `G2` adjoint representation, an Albert-algebra action, or a
Leech-lattice automorphism.
-/

namespace InfoGeometry.Canonical.CyclotomicNestedMatrixRealization

open Matrix
open InfoGeometry.Canonical.CyclotomicExplicitMatrixBridge

abbrev I6 := Sum (Fin 3) (Fin 3)
abbrev I8 := Sum I6 (Fin 2)
abbrev I12 := Sum I8 (Fin 4)
abbrev I16 := Sum I12 (Fin 4)
abbrev I24 := Sum I16 (Fin 8)

/-- First two sectors: tripotent plus complex/radical block. -/
def stage6 : Matrix I6 I6 ℤ :=
  Matrix.fromBlocks tripotent 0 0 complexStage

/-- Add the primitive-sixth-root companion block. -/
def stage8 : Matrix I8 I8 ℤ :=
  Matrix.fromBlocks stage6 0 0 phi6Companion

/-- Add the primitive-eighth-root companion block. -/
def stage12 : Matrix I12 I12 ℤ :=
  Matrix.fromBlocks stage8 0 0 phi8Companion

/-- Add the primitive-twelfth-root companion block. -/
def stage16 : Matrix I16 I16 ℤ :=
  Matrix.fromBlocks stage12 0 0 phi12Companion

/-- Full nested 24-dimensional block operator, with the primitive-24 sector
added last. -/
def nestedStage24 : Matrix I24 I24 ℤ :=
  Matrix.fromBlocks stage16 0 0 phi24Companion

private theorem fromBlocks_zero_pow {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℤ) (D : Matrix n n ℤ) (k : ℕ) :
    (Matrix.fromBlocks A 0 0 D) ^ k =
      Matrix.fromBlocks (A ^ k) 0 0 (D ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp [Matrix.fromBlocks_multiply]
      rw [pow_succ]

/-- The direct-sum carrier has exactly twenty-four basis coordinates. -/
theorem card_I24 : Fintype.card I24 = 24 := by
  native_decide

/-- The complete nested block operator satisfies the common master 25-potent
equation.  This is an exact finite computation on the 24-dimensional direct
sum. -/
theorem nestedStage24_master25_of_blocks
    (ht : tripotent ^ 25 = tripotent)
    (hc : complexStage ^ 25 = complexStage)
    (h6 : phi6Companion ^ 25 = phi6Companion)
    (h8 : phi8Companion ^ 25 = phi8Companion)
    (h12 : phi12Companion ^ 25 = phi12Companion)
    (h24 : phi24Companion ^ 25 = phi24Companion) :
    nestedStage24 ^ 25 = nestedStage24 := by
  rw [nestedStage24, fromBlocks_zero_pow]
  rw [stage16, fromBlocks_zero_pow]
  rw [stage12, fromBlocks_zero_pow]
  rw [stage8, fromBlocks_zero_pow]
  rw [stage6, fromBlocks_zero_pow]
  simp [ht, hc, h6, h8, h12, h24]

/-- Equivalently, the master annihilator vanishes on the assembled finite
operator. -/
theorem nestedStage24_master_annihilator_of_blocks
    (ht : tripotent ^ 25 = tripotent)
    (hc : complexStage ^ 25 = complexStage)
    (h6 : phi6Companion ^ 25 = phi6Companion)
    (h8 : phi8Companion ^ 25 = phi8Companion)
    (h12 : phi12Companion ^ 25 = phi12Companion)
    (h24 : phi24Companion ^ 25 = phi24Companion) :
    nestedStage24 * (nestedStage24 ^ 24 - 1) = 0 := by
  have h := nestedStage24_master25_of_blocks ht hc h6 h8 h12 h24
  calc
    nestedStage24 * (nestedStage24 ^ 24 - 1)
        = nestedStage24 ^ 25 - nestedStage24 := by
            rw [mul_sub, mul_one, ← pow_succ']
    _ = 0 := sub_eq_zero.mpr h

/-- Compact nested-realization packet. -/
theorem nested_cyclotomic_realization_packet
    (ht : tripotent ^ 25 = tripotent)
    (hc : complexStage ^ 25 = complexStage)
    (h6 : phi6Companion ^ 25 = phi6Companion)
    (h8 : phi8Companion ^ 25 = phi8Companion)
    (h12 : phi12Companion ^ 25 = phi12Companion)
    (h24 : phi24Companion ^ 25 = phi24Companion) :
    Fintype.card I24 = 24 ∧
    nestedStage24 ^ 25 = nestedStage24 ∧
    nestedStage24 * (nestedStage24 ^ 24 - 1) = 0 :=
  ⟨card_I24, nestedStage24_master25_of_blocks ht hc h6 h8 h12 h24,
    nestedStage24_master_annihilator_of_blocks ht hc h6 h8 h12 h24⟩

end InfoGeometry.Canonical.CyclotomicNestedMatrixRealization
