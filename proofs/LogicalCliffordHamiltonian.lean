import Mathlib
import proofs.CuntzPeirceLogicalQubit

noncomputable section

open CuntzPeirceLogicalCorner CuntzWordSpaceQEC
open scoped Kronecker

namespace LogicalCliffordHamiltonian

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (S : Fin 2 → A) [hC : CuntzO2 (S 0) (S 1)]

theorem cuntzLogicalMatrixUnit_mul_eq (a b c d : Fin 2) :
    cuntzLogicalMatrixUnit S a b * cuntzLogicalMatrixUnit S c d =
      if b = c then cuntzLogicalMatrixUnit S a d else 0 := by
  unfold cuntzLogicalMatrixUnit
  rw [← CuntzWordSpaceQEC.cuntzWordTwoCornerMap_mul]
  have hraw :
      (PeirceTensorQEC.fibonacciPeircePlusComplex ⊗ₖ Matrix.single a b (1 : ℂ)) *
          (PeirceTensorQEC.fibonacciPeircePlusComplex ⊗ₖ Matrix.single c d (1 : ℂ)) =
        if b = c then
          PeirceTensorQEC.fibonacciPeircePlusComplex ⊗ₖ Matrix.single a d (1 : ℂ)
        else 0 := by
    rw [← Matrix.mul_kronecker_mul]
    rw [PeirceTensorQEC.fibonacciPeircePlusComplex_isOrthogonalProjection.2]
    have hsingle : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 =
        if b = c then Matrix.single a d 1 else 0 := by
      by_cases h : b = c
      · subst c
        ext i j
        fin_cases a <;> fin_cases b <;> fin_cases d <;>
          fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.single]
      · ext i j
        fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
          fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.single, h]
    rw [hsingle]
    by_cases h : b = c <;> simp [h, Matrix.kronecker_zero]
  have hmap := congrArg (cuntzWordTwoCornerMap S) hraw
  by_cases h : b = c
  · simpa [h, CuntzPeirceLogicalCorner.logicalMatrixUnit] using hmap
  · simpa [h, CuntzPeirceLogicalCorner.logicalMatrixUnit,
      CuntzWordSpaceQEC.cuntzWordTwoCornerMap_zero] using hmap

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
  abel

theorem logicalSigmaX_sq :
    logicalSigmaX S * logicalSigmaX S = logicalCodeUnit S := by
  unfold logicalSigmaX logicalCodeUnit
  simp only [mul_add, add_mul]
  have h1 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 0 1 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 1 0 = cuntzLogicalMatrixUnit S 0 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 0 1 = cuntzLogicalMatrixUnit S 1 1 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 1 0 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4]
  abel

theorem logicalSigmaZ_anticommute_logicalSigmaX :
    logicalSigmaZ S * logicalSigmaX S + logicalSigmaX S * logicalSigmaZ S = 0 := by
  unfold logicalSigmaZ logicalSigmaX
  simp only [sub_mul, mul_add, add_mul, mul_sub]
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 0 1 = cuntzLogicalMatrixUnit S 0 1 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 1 0 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 0 1 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 1 0 = cuntzLogicalMatrixUnit S 1 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h5 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 0 0 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h6 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 1 1 = cuntzLogicalMatrixUnit S 0 1 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h7 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 0 0 = cuntzLogicalMatrixUnit S 1 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h8 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 1 1 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  noncomm_ring

theorem logicalCodeUnit_mul_codeUnit :
    logicalCodeUnit S * logicalCodeUnit S = logicalCodeUnit S := by
  unfold logicalCodeUnit
  simp only [add_mul, mul_add, cuntzLogicalMatrixUnit_mul_eq] <;> try simp

theorem logicalCodeUnit_mul_logicalSigmaZ :
    logicalCodeUnit S * logicalSigmaZ S = logicalSigmaZ S := by
  unfold logicalCodeUnit logicalSigmaZ
  simp only [add_mul, mul_sub, cuntzLogicalMatrixUnit_mul_eq] <;> try simp <;> abel

theorem logicalSigmaZ_mul_codeUnit :
    logicalSigmaZ S * logicalCodeUnit S = logicalSigmaZ S := by
  unfold logicalCodeUnit logicalSigmaZ
  simp only [sub_mul, add_mul, mul_add, cuntzLogicalMatrixUnit_mul_eq] <;> try simp <;> abel

theorem logicalCodeUnit_mul_logicalSigmaX :
    logicalCodeUnit S * logicalSigmaX S = logicalSigmaX S := by
  unfold logicalCodeUnit logicalSigmaX
  simp only [add_mul, mul_add, cuntzLogicalMatrixUnit_mul_eq] <;> try simp <;> abel

theorem logicalSigmaX_mul_codeUnit :
    logicalSigmaX S * logicalCodeUnit S = logicalSigmaX S := by
  unfold logicalCodeUnit logicalSigmaX
  simp only [add_mul, mul_add, cuntzLogicalMatrixUnit_mul_eq] <;> try simp <;> abel

def logicalWDWHamiltonian (t x y : ℝ) : A :=
  (t : ℂ) • logicalCodeUnit S +
  (x : ℂ) • logicalSigmaZ S +
  (y : ℂ) • logicalSigmaX S

def logicalWDWConjugate (t x y : ℝ) : A :=
  (t : ℂ) • logicalCodeUnit S -
  (x : ℂ) • logicalSigmaZ S -
  (y : ℂ) • logicalSigmaX S

-- Expanding and proving the factorization utilizing the relations above
theorem logicalWDWHamiltonian_mul_conjugate (t x y : ℝ) :
    logicalWDWHamiltonian S t x y * logicalWDWConjugate S t x y =
      algebraMap ℂ A ((t ^ 2 - x ^ 2 - y ^ 2 : ℝ) : ℂ) * logicalCodeUnit S := by
  unfold logicalWDWHamiltonian logicalWDWConjugate
  have hCC := logicalCodeUnit_mul_codeUnit S
  have hCZ := logicalCodeUnit_mul_logicalSigmaZ S
  have hZC := logicalSigmaZ_mul_codeUnit S
  have hCX := logicalCodeUnit_mul_logicalSigmaX S
  have hXC := logicalSigmaX_mul_codeUnit S
  have hZZ := logicalSigmaZ_sq S
  have hXX := logicalSigmaX_sq S
  have hZX : logicalSigmaZ S * logicalSigmaX S =
      -(logicalSigmaX S * logicalSigmaZ S) := by
    have h := logicalSigmaZ_anticommute_logicalSigmaX S
    calc
      logicalSigmaZ S * logicalSigmaX S =
          logicalSigmaZ S * logicalSigmaX S + logicalSigmaX S * logicalSigmaZ S -
            logicalSigmaX S * logicalSigmaZ S := by abel
      _ = 0 - logicalSigmaX S * logicalSigmaZ S := by rw [h]
      _ = -(logicalSigmaX S * logicalSigmaZ S) := by rw [zero_sub]
  have hXZ : logicalSigmaX S * logicalSigmaZ S =
      -(logicalSigmaZ S * logicalSigmaX S) := by
    rw [hZX]
    simp
  rw [← Algebra.smul_def]
  simp only [add_mul, sub_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  rw [hCC, hCZ, hCX, hZC, hXC, hZZ, hXX, hZX]
  push_cast
  module

theorem logicalWDWConjugate_mul_hamiltonian (t x y : ℝ) :
    logicalWDWConjugate S t x y * logicalWDWHamiltonian S t x y =
      algebraMap ℂ A ((t ^ 2 - x ^ 2 - y ^ 2 : ℝ) : ℂ) * logicalCodeUnit S := by
  unfold logicalWDWHamiltonian logicalWDWConjugate
  have hCC := logicalCodeUnit_mul_codeUnit S
  have hCZ := logicalCodeUnit_mul_logicalSigmaZ S
  have hZC := logicalSigmaZ_mul_codeUnit S
  have hCX := logicalCodeUnit_mul_logicalSigmaX S
  have hXC := logicalSigmaX_mul_codeUnit S
  have hZZ := logicalSigmaZ_sq S
  have hXX := logicalSigmaX_sq S
  have hZX : logicalSigmaZ S * logicalSigmaX S =
      -(logicalSigmaX S * logicalSigmaZ S) := by
    have h := logicalSigmaZ_anticommute_logicalSigmaX S
    calc
      logicalSigmaZ S * logicalSigmaX S =
          logicalSigmaZ S * logicalSigmaX S + logicalSigmaX S * logicalSigmaZ S -
            logicalSigmaX S * logicalSigmaZ S := by abel
      _ = 0 - logicalSigmaX S * logicalSigmaZ S := by rw [h]
      _ = -(logicalSigmaX S * logicalSigmaZ S) := by rw [zero_sub]
  have hXZ : logicalSigmaX S * logicalSigmaZ S =
      -(logicalSigmaZ S * logicalSigmaX S) := by
    rw [hZX]
    simp
  rw [← Algebra.smul_def]
  simp only [add_mul, sub_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  rw [hCC, hCZ, hCX, hZC, hXC, hZZ, hXX, hZX]
  push_cast
  module

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
theorem logicalWDWMatrix_eq_zero_iff (t x y : ℝ) :
    logicalWDWMatrix t x y = 0 ↔ t = 0 ∧ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h00 := congrArg (fun M => M 0 0) h
    have h01 := congrArg (fun M => M 0 1) h
    have h11 := congrArg (fun M => M 1 1) h
    have h00c : ((t + x : ℝ) : ℂ) = 0 := by simpa [logicalWDWMatrix] using h00
    have h01c : ((y : ℝ) : ℂ) = 0 := by simpa [logicalWDWMatrix] using h01
    have h11c : ((t - x : ℝ) : ℂ) = 0 := by simpa [logicalWDWMatrix] using h11
    have h00' : t + x = 0 := by exact_mod_cast h00c
    have h01' : y = 0 := by exact_mod_cast h01c
    have h11' : t - x = 0 := by exact_mod_cast h11c
    exact ⟨by linarith, by linarith, h01'⟩
  · rintro ⟨rfl, rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [logicalWDWMatrix]

def logicalMatrixEmbedding (M : Matrix (Fin 2) (Fin 2) ℂ) : A :=
  M 0 0 • cuntzLogicalMatrixUnit S 0 0 +
  M 0 1 • cuntzLogicalMatrixUnit S 0 1 +
  M 1 0 • cuntzLogicalMatrixUnit S 1 0 +
  M 1 1 • cuntzLogicalMatrixUnit S 1 1

theorem logicalWDWHamiltonian_eq_embedding (t x y : ℝ) :
    logicalWDWHamiltonian S t x y = logicalMatrixEmbedding S (logicalWDWMatrix t x y)
    := by
  unfold logicalWDWHamiltonian logicalMatrixEmbedding logicalWDWMatrix
    logicalCodeUnit logicalSigmaZ logicalSigmaX
  simp [logicalWDWHamiltonian, logicalMatrixEmbedding, logicalWDWMatrix,
    logicalCodeUnit, logicalSigmaZ, logicalSigmaX, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  have hreal (r : ℝ) (z : A) : r • z = (r : ℂ) • z := rfl
  simp_rw [hreal]
  module

theorem logicalMatrixEmbedding_zero : logicalMatrixEmbedding S 0 = 0 := by
  simp [logicalMatrixEmbedding]

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

theorem logicalWDWConjugate_eq_embedding (t x y : ℝ) :
    logicalWDWConjugate S t x y = logicalMatrixEmbedding S (logicalWDWConjugateMatrix t x y)
    := by
  unfold logicalWDWConjugate logicalMatrixEmbedding logicalWDWConjugateMatrix
    logicalCodeUnit logicalSigmaZ logicalSigmaX
  simp [logicalWDWConjugate, logicalMatrixEmbedding, logicalWDWConjugateMatrix,
    logicalCodeUnit, logicalSigmaZ, logicalSigmaX, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  have hreal (r : ℝ) (z : A) : r • z = (r : ℂ) • z := rfl
  simp_rw [hreal]
  module

theorem logicalWDWConjugateMatrix_eq_zero_iff (t x y : ℝ) :
    logicalWDWConjugateMatrix t x y = 0 ↔ t = 0 ∧ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h00 := congrArg (fun M => M 0 0) h
    have h01 := congrArg (fun M => M 0 1) h
    have h11 := congrArg (fun M => M 1 1) h
    have h00c : ((t - x : ℝ) : ℂ) = 0 := by simpa [logicalWDWConjugateMatrix] using h00
    have h01c : ((-y : ℝ) : ℂ) = 0 := by simpa [logicalWDWConjugateMatrix] using h01
    have h11c : ((t + x : ℝ) : ℂ) = 0 := by simpa [logicalWDWConjugateMatrix] using h11
    have h00' : t - x = 0 := by exact_mod_cast h00c
    have h01' : y = 0 := by
      have : -y = 0 := by exact_mod_cast h01c
      linarith
    have h11' : t + x = 0 := by exact_mod_cast h11c
    exact ⟨by linarith, by linarith, h01'⟩
  · rintro ⟨rfl, rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [logicalWDWConjugateMatrix]

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
