import InfoGeometry.Cantor.CliffordSymmetryGroup

/-!
# Multiplication defect of averaged Fock symmetries

Dependency order: split Clifford representation → CAR operators → permutation
conjugation → linear averaging → multiplication defect. All products below
are compositions in the full Fock endomorphism algebra.
-/

noncomputable section

namespace InfoGeometry.Cantor.CliffordMarkovDefect

open InfoGeometry.Clifford.ClNNFockRepresentation
open InfoGeometry.Clifford.FockSpaceCAR
open InfoGeometry.Clifford.ClNNPermutationSymmetry
open InfoGeometry.Cantor.CliffordMarkovOperators

variable (n : ℕ)

abbrev Operators := Module.End ℝ (FockSpace (PrimalSheet n))

/-- The equal-weight average of identity and a permutation conjugation. -/
def midpoint (σ : Equiv.Perm (Fin n)) : Operators n →ₗ[ℝ] Operators n :=
  (1 / 2 : ℝ) • (LinearMap.id + (fockOperatorPermutationEquiv n σ).toLinearMap)

theorem midpoint_apply (σ : Equiv.Perm (Fin n)) (A : Operators n) :
    midpoint n σ A = (1 / 2 : ℝ) • (A + fockOperatorPermutationEquiv n σ A) := rfl

theorem midpoint_one (σ : Equiv.Perm (Fin n)) : midpoint n σ 1 = 1 := by
  simp only [midpoint_apply, map_one]
  module

/-- The exact failure of multiplication preservation, with the factor order
retained. No commutativity of the operators is assumed. -/
theorem midpoint_mul_defect (σ : Equiv.Perm (Fin n)) (A B : Operators n) :
    midpoint n σ (A * B) - midpoint n σ A * midpoint n σ B =
      (1 / 4 : ℝ) •
        ((A - fockOperatorPermutationEquiv n σ A) *
          (B - fockOperatorPermutationEquiv n σ B)) := by
  simp only [midpoint_apply, map_mul, smul_mul_assoc, mul_smul_comm,
    add_mul, mul_add, sub_mul, mul_sub]
  module

/-- Multiplication is preserved on a pair precisely when the ordered product
of their permutation differences vanishes. Neither difference must vanish
individually in this operator algebra. -/
theorem midpoint_mul_iff (σ : Equiv.Perm (Fin n)) (A B : Operators n) :
    midpoint n σ (A * B) = midpoint n σ A * midpoint n σ B ↔
      (A - fockOperatorPermutationEquiv n σ A) *
        (B - fockOperatorPermutationEquiv n σ B) = 0 := by
  rw [← sub_eq_zero, midpoint_mul_defect]
  simp only [smul_eq_zero]
  norm_num

/-- A fixed left factor is sufficient for multiplication preservation. -/
theorem midpoint_mul_of_left_fixed (σ : Equiv.Perm (Fin n)) (A B : Operators n)
    (hA : fockOperatorPermutationEquiv n σ A = A) :
    midpoint n σ (A * B) = midpoint n σ A * midpoint n σ B := by
  apply (midpoint_mul_iff n σ A B).mpr
  rw [hA, sub_self, zero_mul]

/-- A fixed right factor is sufficient, with the original order retained. -/
theorem midpoint_mul_of_right_fixed (σ : Equiv.Perm (Fin n)) (A B : Operators n)
    (hB : fockOperatorPermutationEquiv n σ B = B) :
    midpoint n σ (A * B) = midpoint n σ A * midpoint n σ B := by
  apply (midpoint_mul_iff n σ A B).mpr
  rw [hB, sub_self, mul_zero]

/-- Swapping two distinct Clifford modes and averaging with identity sends
either mode to their midpoint. -/
theorem midpoint_swap_mode (i j : Fin n) :
    midpoint n (Equiv.swap i j) (cantorModeCliffordOperator n i) =
      (1 / 2 : ℝ) •
        (cantorModeCliffordOperator n i + cantorModeCliffordOperator n j) := by
  simp only [midpoint_apply, fockPermutation_conj_cantorMode, Equiv.swap_apply_left]

/-- The averaged mode has square one-half of the identity operator. -/
theorem midpoint_swap_mode_square {i j : Fin n} (hij : i ≠ j) :
    midpoint n (Equiv.swap i j) (cantorModeCliffordOperator n i) *
      midpoint n (Equiv.swap i j) (cantorModeCliffordOperator n i) =
        (1 / 2 : ℝ) • (1 : Operators n) := by
  rw [midpoint_swap_mode, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hsum :
      (cantorModeCliffordOperator n i + cantorModeCliffordOperator n j) *
        (cantorModeCliffordOperator n i + cantorModeCliffordOperator n j) =
          (1 : Operators n) + 1 := by
    have hcar := cantorModeCliffordOperator_cross_CAR n hij
    have hi := cantorModeCliffordOperator_sq n i
    have hj := cantorModeCliffordOperator_sq n j
    calc
      _ = cantorModeCliffordOperator n i * cantorModeCliffordOperator n i +
          cantorModeCliffordOperator n j * cantorModeCliffordOperator n j +
          (cantorModeCliffordOperator n i * cantorModeCliffordOperator n j +
            cantorModeCliffordOperator n j * cantorModeCliffordOperator n i) := by
        noncomm_ring
      _ = _ := by rw [hi, hj, hcar, add_zero]
  rw [hsum]
  module

/-- This stochastic average is not multiplicative, witnessed by a genuine
Clifford mode in the noncommutative Fock operator algebra. -/
theorem midpoint_swap_not_multiplicative {i j : Fin n} (hij : i ≠ j) :
    ¬ ∀ A B : Operators n,
      midpoint n (Equiv.swap i j) (A * B) =
        midpoint n (Equiv.swap i j) A * midpoint n (Equiv.swap i j) B := by
  intro h
  have heq := h (cantorModeCliffordOperator n i) (cantorModeCliffordOperator n i)
  rw [cantorModeCliffordOperator_sq, midpoint_one,
    midpoint_swap_mode_square n hij] at heq
  have hz : ((1 / 2 : ℝ) - 1) • (1 : Operators n) = 0 := by
    calc
      _ = (1 / 2 : ℝ) • (1 : Operators n) - 1 := by module
      _ = 0 := by rw [← heq, sub_self]
  rcases smul_eq_zero.mp hz with hc | ho
  · norm_num at hc
  · exact one_ne_zero ho

end InfoGeometry.Cantor.CliffordMarkovDefect
