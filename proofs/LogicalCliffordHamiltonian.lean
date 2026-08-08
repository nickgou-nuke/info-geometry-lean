import Mathlib
import proofs.CuntzPeirceLogicalQubit

noncomputable section

open CuntzPeirceLogicalCorner CuntzWordSpaceQEC

namespace LogicalCliffordHamiltonian

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (S : Fin 2 → A) [hC : CuntzO2 (S 0) (S 1)]

axiom cuntzLogicalMatrixUnit_mul_eq (a b c d : Fin 2) :
    cuntzLogicalMatrixUnit S a b * cuntzLogicalMatrixUnit S c d =
      if b = c then cuntzLogicalMatrixUnit S a d else 0

def logicalCodeUnit : A :=
  cuntzLogicalMatrixUnit S 0 0 + cuntzLogicalMatrixUnit S 1 1

def logicalSigmaZ : A :=
  cuntzLogicalMatrixUnit S 0 0 - cuntzLogicalMatrixUnit S 1 1

def logicalSigmaX : A :=
  cuntzLogicalMatrixUnit S 0 1 + cuntzLogicalMatrixUnit S 1 0

theorem logicalSigmaZ_sq :
    logicalSigmaZ S * logicalSigmaZ S = logicalCodeUnit S := by
  unfold logicalSigmaZ logicalCodeUnit
  rw [sub_mul, mul_sub, mul_sub]
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 0 0 = cuntzLogicalMatrixUnit S 0 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 1 1 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 0 0 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 1 1 = cuntzLogicalMatrixUnit S 1 1 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4]
  ring

theorem logicalSigmaX_sq :
    logicalSigmaX S * logicalSigmaX S = logicalCodeUnit S := by
  unfold logicalSigmaX logicalCodeUnit
  rw [add_mul, mul_add, add_mul]
  have h1 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 0 1 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 1 0 = cuntzLogicalMatrixUnit S 0 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 0 1 = cuntzLogicalMatrixUnit S 1 1 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 1 0 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4]
  ring

theorem logicalSigmaZ_anticommute_logicalSigmaX :
    logicalSigmaZ S * logicalSigmaX S + logicalSigmaX S * logicalSigmaZ S = 0 := by
  unfold logicalSigmaZ logicalSigmaX
  rw [sub_mul, mul_add, mul_add, add_mul, mul_sub, mul_sub]
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 0 1 = cuntzLogicalMatrixUnit S 0 1 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 1 0 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 0 1 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 1 0 = cuntzLogicalMatrixUnit S 1 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h5 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 0 0 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h6 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 1 1 = cuntzLogicalMatrixUnit S 0 1 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h7 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 0 0 = cuntzLogicalMatrixUnit S 1 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h8 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 1 1 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  ring

def logicalWDWHamiltonian (t x y : ℝ) : A :=
  (t : ℂ) • logicalCodeUnit S +
  (x : ℂ) • logicalSigmaZ S +
  (y : ℂ) • logicalSigmaX S

def logicalWDWConjugate (t x y : ℝ) : A :=
  (t : ℂ) • logicalCodeUnit S -
  (x : ℂ) • logicalSigmaZ S -
  (y : ℂ) • logicalSigmaX S

-- Expanding and proving the factorization utilizing the relations above
axiom logicalWDWHamiltonian_mul_conjugate (t x y : ℝ) :
    logicalWDWHamiltonian S t x y * logicalWDWConjugate S t x y =
      algebraMap ℂ A ((t ^ 2 - x ^ 2 - y ^ 2 : ℝ) : ℂ) * logicalCodeUnit S

axiom logicalWDWConjugate_mul_hamiltonian (t x y : ℝ) :
    logicalWDWConjugate S t x y * logicalWDWHamiltonian S t x y =
      algebraMap ℂ A ((t ^ 2 - x ^ 2 - y ^ 2 : ℝ) : ℂ) * logicalCodeUnit S

theorem logicalWDWHamiltonian_mul_conjugate_of_null (t x y : ℝ)
    (hnull : t ^ 2 - x ^ 2 - y ^ 2 = 0) :
    logicalWDWHamiltonian S t x y * logicalWDWConjugate S t x y = 0 := by
  rw [logicalWDWHamiltonian_mul_conjugate]
  rw [hnull]
  simp

def logicalWDWMatrix (t x y : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(t + x : ℝ), y;
     y, t - x]

def logicalWDWConjugateMatrix (t x y : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(t - x : ℝ), -y;
     -y, t + x]

-- The kernel identification for the Matrix representation
axiom logicalWDWMatrix_eq_zero_iff (t x y : ℝ) :
    logicalWDWMatrix t x y = 0 ↔ t = 0 ∧ x = 0 ∧ y = 0

def logicalMatrixEmbedding (M : Matrix (Fin 2) (Fin 2) ℂ) : A :=
  M 0 0 • cuntzLogicalMatrixUnit S 0 0 +
  M 0 1 • cuntzLogicalMatrixUnit S 0 1 +
  M 1 0 • cuntzLogicalMatrixUnit S 1 0 +
  M 1 1 • cuntzLogicalMatrixUnit S 1 1

axiom logicalWDWHamiltonian_eq_embedding (t x y : ℝ) :
    logicalWDWHamiltonian S t x y = logicalMatrixEmbedding S (logicalWDWMatrix t x y)

axiom logicalMatrixEmbedding_zero : logicalMatrixEmbedding S 0 = 0

theorem logicalWDWHamiltonian_ne_zero (t x y : ℝ)
    (h_inj : Function.Injective (logicalMatrixEmbedding S))
    (hxyz : ¬ (t = 0 ∧ x = 0 ∧ y = 0)) :
    logicalWDWHamiltonian S t x y ≠ 0 := by
  intro hH
  apply hxyz
  apply (logicalWDWMatrix_eq_zero_iff t x y).mp
  apply h_inj
  rw [← logicalWDWHamiltonian_eq_embedding S t x y]
  rw [logicalMatrixEmbedding_zero S]
  exact hH

axiom logicalWDWConjugate_eq_embedding (t x y : ℝ) :
    logicalWDWConjugate S t x y = logicalMatrixEmbedding S (logicalWDWConjugateMatrix t x y)

axiom logicalWDWConjugateMatrix_eq_zero_iff (t x y : ℝ) :
    logicalWDWConjugateMatrix t x y = 0 ↔ t = 0 ∧ x = 0 ∧ y = 0

theorem logicalWDWConjugate_ne_zero (t x y : ℝ)
    (h_inj : Function.Injective (logicalMatrixEmbedding S))
    (hxyz : ¬ (t = 0 ∧ x = 0 ∧ y = 0)) :
    logicalWDWConjugate S t x y ≠ 0 := by
  intro hH
  apply hxyz
  apply (logicalWDWConjugateMatrix_eq_zero_iff t x y).mp
  apply h_inj
  rw [← logicalWDWConjugate_eq_embedding S t x y]
  rw [logicalMatrixEmbedding_zero S]
  exact hH

def IsNonzeroMutualZeroDivisor (a b : A) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 ∧ b * a = 0

theorem logicalWDW_nontrivial_zero_divisor_pair (t x y : ℝ)
    (h_inj : Function.Injective (logicalMatrixEmbedding S))
    (hnull : t ^ 2 - x ^ 2 - y ^ 2 = 0)
    (hnonzero : t ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0) :
    IsNonzeroMutualZeroDivisor (logicalWDWHamiltonian S t x y) (logicalWDWConjugate S t x y) := by
  have hxyz : ¬ (t = 0 ∧ x = 0 ∧ y = 0) := by
    intro h
    rcases h with ⟨ht, hx, hy⟩
    rcases hnonzero with h | h | h
    · exact h ht
    · exact h hx
    · exact h hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact logicalWDWHamiltonian_ne_zero S t x y h_inj hxyz
  · exact logicalWDWConjugate_ne_zero S t x y h_inj hxyz
  · exact logicalWDWHamiltonian_mul_conjugate_of_null S t x y hnull
  · rw [logicalWDWConjugate_mul_hamiltonian, hnull]
    simp

end LogicalCliffordHamiltonian
