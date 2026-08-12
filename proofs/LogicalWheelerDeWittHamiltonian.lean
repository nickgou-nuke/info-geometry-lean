import Mathlib
import proofs.CuntzPeirceLogicalQubit
import proofs.CuntzWordSpaceQEC
import proofs.LogicalCliffordHamiltonian

noncomputable section

open Matrix CuntzWordSpaceQEC CuntzPeirceLogicalCorner

namespace LogicalWheelerDeWittHamiltonian

variable {A : Type*}
variable [Ring A] [StarRing A]
variable [Algebra ℂ A] [StarModule ℂ A]
variable (S : Fin 2 → A) [hC : CuntzO2 (S 0) (S 1)]

def logicalCodeUnit : A :=
  cuntzLogicalMatrixUnit S 0 0 + cuntzLogicalMatrixUnit S 1 1

def logicalSigmaZ : A :=
  cuntzLogicalMatrixUnit S 0 0 - cuntzLogicalMatrixUnit S 1 1

def logicalSigmaX : A :=
  cuntzLogicalMatrixUnit S 0 1 + cuntzLogicalMatrixUnit S 1 0

theorem cuntzLogicalMatrixUnit_mul_eq (a b c d : Fin 2) :
    cuntzLogicalMatrixUnit S a b * cuntzLogicalMatrixUnit S c d =
      if b = c then cuntzLogicalMatrixUnit S a d else 0 := by
  simpa [CuntzPeirceLogicalCorner.cuntzLogicalMatrixUnit,
    CuntzPeirceLogicalCorner.logicalMatrixUnit,
    CuntzWordSpaceQEC.logicalMatrixUnit] using
    (CuntzWordSpaceQEC.logicalMatrixUnit_mul S a b c d)

theorem logicalCodeUnit_idempotent :
    logicalCodeUnit S * logicalCodeUnit S = logicalCodeUnit S := by
  unfold logicalCodeUnit
  rw [add_mul, mul_add, mul_add]
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 0 0 = cuntzLogicalMatrixUnit S 0 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 1 1 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 0 0 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 1 1 = cuntzLogicalMatrixUnit S 1 1 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4]
  abel

theorem logicalCodeUnit_mul_logicalSigmaZ :
    logicalCodeUnit S * logicalSigmaZ S = logicalSigmaZ S := by
  exact LogicalCliffordHamiltonian.logicalCodeUnit_mul_logicalSigmaZ S

theorem logicalSigmaZ_mul_logicalCodeUnit :
    logicalSigmaZ S * logicalCodeUnit S = logicalSigmaZ S := by
  unfold logicalCodeUnit logicalSigmaZ
  rw [sub_mul, mul_add, mul_add]
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 0 0 = cuntzLogicalMatrixUnit S 0 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 1 1 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 0 0 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 1 1 = cuntzLogicalMatrixUnit S 1 1 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4]
  simp

theorem logicalCodeUnit_mul_logicalSigmaX :
    logicalCodeUnit S * logicalSigmaX S = logicalSigmaX S := by
  unfold logicalCodeUnit logicalSigmaX
  rw [add_mul, mul_add, mul_add]
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 0 1 = cuntzLogicalMatrixUnit S 0 1 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 1 0 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 0 1 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 1 0 = cuntzLogicalMatrixUnit S 1 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4]
  simp

theorem logicalSigmaX_mul_logicalCodeUnit :
    logicalSigmaX S * logicalCodeUnit S = logicalSigmaX S := by
  unfold logicalCodeUnit logicalSigmaX
  rw [add_mul, mul_add, mul_add]
  have h1 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 0 0 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 1 1 = cuntzLogicalMatrixUnit S 0 1 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 0 0 = cuntzLogicalMatrixUnit S 1 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 1 1 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4]
  simp

theorem logicalSigmaZ_sq :
    logicalSigmaZ S * logicalSigmaZ S = logicalCodeUnit S := by
  unfold logicalSigmaZ logicalCodeUnit
  rw [sub_mul, mul_sub, mul_sub]
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 0 0 = cuntzLogicalMatrixUnit S 0 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 1 1 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 0 0 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 1 1 = cuntzLogicalMatrixUnit S 1 1 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4]
  abel

theorem logicalSigmaX_sq :
    logicalSigmaX S * logicalSigmaX S = logicalCodeUnit S := by
  unfold logicalSigmaX logicalCodeUnit
  rw [add_mul, mul_add, mul_add]
  have h1 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 0 1 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 1 0 = cuntzLogicalMatrixUnit S 0 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 0 1 = cuntzLogicalMatrixUnit S 1 1 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 1 0 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4]
  abel

theorem logicalSigmaZ_anticommute_logicalSigmaX :
    logicalSigmaZ S * logicalSigmaX S + logicalSigmaX S * logicalSigmaZ S = 0 := by
  unfold logicalSigmaZ logicalSigmaX
  rw [sub_mul, mul_add, mul_add, add_mul, mul_sub, mul_sub]
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 0 1 = cuntzLogicalMatrixUnit S 0 1 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 1 0 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 0 1 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 1 0 = cuntzLogicalMatrixUnit S 1 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h5 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 0 0 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h6 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 1 1 = cuntzLogicalMatrixUnit S 0 1 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h7 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 0 0 = cuntzLogicalMatrixUnit S 1 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h8 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 1 1 = 0 := by
    rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  abel

def logicalWDWHamiltonian (t x y : ℝ) : A :=
  (t : ℂ) • logicalCodeUnit S +
  (x : ℂ) • logicalSigmaZ S +
  (y : ℂ) • logicalSigmaX S

def logicalWDWConjugate (t x y : ℝ) : A :=
  (t : ℂ) • logicalCodeUnit S -
  (x : ℂ) • logicalSigmaZ S -
  (y : ℂ) • logicalSigmaX S

theorem logicalWDWHamiltonian_left_support (t x y : ℝ) :
    logicalCodeUnit S * logicalWDWHamiltonian S t x y = logicalWDWHamiltonian S t x y := by
  unfold logicalWDWHamiltonian
  rw [mul_add, mul_add]
  rw [mul_smul_comm, mul_smul_comm, mul_smul_comm]
  rw [logicalCodeUnit_idempotent S, logicalCodeUnit_mul_logicalSigmaZ S, logicalCodeUnit_mul_logicalSigmaX S]

theorem logicalWDWHamiltonian_right_support (t x y : ℝ) :
    logicalWDWHamiltonian S t x y * logicalCodeUnit S = logicalWDWHamiltonian S t x y := by
  unfold logicalWDWHamiltonian
  rw [add_mul, add_mul]
  rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
  rw [logicalCodeUnit_idempotent S, logicalSigmaZ_mul_logicalCodeUnit S, logicalSigmaX_mul_logicalCodeUnit S]

theorem logicalWDWConjugate_left_support (t x y : ℝ) :
    logicalCodeUnit S * logicalWDWConjugate S t x y = logicalWDWConjugate S t x y := by
  unfold logicalWDWConjugate
  rw [mul_sub, mul_sub]
  rw [mul_smul_comm, mul_smul_comm, mul_smul_comm]
  rw [logicalCodeUnit_idempotent S, logicalCodeUnit_mul_logicalSigmaZ S, logicalCodeUnit_mul_logicalSigmaX S]

theorem logicalWDWConjugate_right_support (t x y : ℝ) :
    logicalWDWConjugate S t x y * logicalCodeUnit S = logicalWDWConjugate S t x y := by
  unfold logicalWDWConjugate
  rw [sub_mul, sub_mul]
  rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc]
  rw [logicalCodeUnit_idempotent S, logicalSigmaZ_mul_logicalCodeUnit S, logicalSigmaX_mul_logicalCodeUnit S]

theorem logicalSigmaZ_star : star (logicalSigmaZ S) = logicalSigmaZ S := by
  unfold logicalSigmaZ
  rw [star_sub]
  have hstar (a b : Fin 2) :
      star (cuntzLogicalMatrixUnit S a b) = cuntzLogicalMatrixUnit S b a := by
    simpa [CuntzPeirceLogicalCorner.cuntzLogicalMatrixUnit,
      CuntzPeirceLogicalCorner.logicalMatrixUnit,
      CuntzWordSpaceQEC.logicalMatrixUnit] using
      (CuntzWordSpaceQEC.logicalMatrixUnit_star S a b)
  rw [hstar, hstar]

theorem logicalSigmaX_star : star (logicalSigmaX S) = logicalSigmaX S := by
  unfold logicalSigmaX
  rw [star_add]
  have hstar (a b : Fin 2) :
      star (cuntzLogicalMatrixUnit S a b) = cuntzLogicalMatrixUnit S b a := by
    simpa [CuntzPeirceLogicalCorner.cuntzLogicalMatrixUnit,
      CuntzPeirceLogicalCorner.logicalMatrixUnit,
      CuntzWordSpaceQEC.logicalMatrixUnit] using
      (CuntzWordSpaceQEC.logicalMatrixUnit_star S a b)
  rw [hstar, hstar]
  rw [add_comm]

theorem logicalCodeUnit_star : star (logicalCodeUnit S) = logicalCodeUnit S := by
  unfold logicalCodeUnit
  rw [star_add]
  have hstar (a b : Fin 2) :
      star (cuntzLogicalMatrixUnit S a b) = cuntzLogicalMatrixUnit S b a := by
    simpa [CuntzPeirceLogicalCorner.cuntzLogicalMatrixUnit,
      CuntzPeirceLogicalCorner.logicalMatrixUnit,
      CuntzWordSpaceQEC.logicalMatrixUnit] using
      (CuntzWordSpaceQEC.logicalMatrixUnit_star S a b)
  rw [hstar, hstar]

theorem logicalWDWHamiltonian_selfAdjoint (t x y : ℝ) :
    star (logicalWDWHamiltonian S t x y) = logicalWDWHamiltonian S t x y := by
  unfold logicalWDWHamiltonian
  rw [star_add, star_add, star_smul, star_smul, star_smul]
  rw [logicalCodeUnit_star S, logicalSigmaZ_star S, logicalSigmaX_star S]
  simp

theorem logicalWDWConjugate_selfAdjoint (t x y : ℝ) :
    star (logicalWDWConjugate S t x y) = logicalWDWConjugate S t x y := by
  unfold logicalWDWConjugate
  rw [star_sub, star_sub, star_smul, star_smul, star_smul]
  rw [logicalCodeUnit_star S, logicalSigmaZ_star S, logicalSigmaX_star S]
  simp

private theorem smul_mul_smul_assoc (r s : ℂ) (u v : A) :
    (r • u) * (s • v) = (r * s) • (u * v) := by
  calc
    (r • u) * (s • v) = r • (u * (s • v)) := by rw [smul_mul_assoc]
    _ = r • (s • (u * v)) := by rw [mul_smul_comm]
    _ = (r * s) • (u * v) := by rw [smul_smul]

theorem logicalWDWHamiltonian_mul_conjugate (t x y : ℝ) :
    logicalWDWHamiltonian S t x y * logicalWDWConjugate S t x y =
      algebraMap ℂ A ((t ^ 2 - x ^ 2 - y ^ 2 : ℝ) : ℂ) * logicalCodeUnit S := by
  exact LogicalCliffordHamiltonian.logicalWDWHamiltonian_mul_conjugate S t x y

theorem logicalWDWConjugate_mul_hamiltonian (t x y : ℝ) :
    logicalWDWConjugate S t x y * logicalWDWHamiltonian S t x y =
      algebraMap ℂ A ((t ^ 2 - x ^ 2 - y ^ 2 : ℝ) : ℂ) * logicalCodeUnit S := by
  exact LogicalCliffordHamiltonian.logicalWDWConjugate_mul_hamiltonian S t x y

theorem logicalWDWHamiltonian_mul_conjugate_of_null (t x y : ℝ)
    (hnull : t ^ 2 - x ^ 2 - y ^ 2 = 0) :
    logicalWDWHamiltonian S t x y * logicalWDWConjugate S t x y = 0 := by
  rw [logicalWDWHamiltonian_mul_conjugate S t x y]
  rw [hnull]
  simp

theorem logicalWDWHamiltonian_inverse_in_corner
    (t x y : ℝ)
    (hq : t ^ 2 - x ^ 2 - y ^ 2 ≠ 0) :
    let q : ℂ := (t ^ 2 - x ^ 2 - y ^ 2 : ℝ)
    logicalWDWHamiltonian S t x y *
        (q⁻¹ • logicalWDWConjugate S t x y) =
      logicalCodeUnit S
    ∧
    (q⁻¹ • logicalWDWConjugate S t x y) *
        logicalWDWHamiltonian S t x y =
      logicalCodeUnit S := by
  dsimp
  have hq_c : ((t^2 - x^2 - y^2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq
  constructor
  · rw [mul_smul_comm]
    rw [logicalWDWHamiltonian_mul_conjugate]
    rw [Algebra.smul_def]
    rw [← mul_assoc]
    rw [← map_mul, inv_mul_cancel₀ hq_c, map_one, one_mul]
  · rw [smul_mul_assoc]
    rw [logicalWDWConjugate_mul_hamiltonian]
    rw [Algebra.smul_def]
    rw [← mul_assoc]
    rw [← map_mul, inv_mul_cancel₀ hq_c, map_one, one_mul]

def IsNonzeroMutualZeroDivisor (a b : A) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 ∧ b * a = 0

theorem logicalWDW_null_gives_nonzeroMutualZeroDivisor
    (t x y : ℝ)
    (hnull : t ^ 2 - x ^ 2 - y ^ 2 = 0)
    (hH : logicalWDWHamiltonian S t x y ≠ 0)
    (hHs : logicalWDWConjugate S t x y ≠ 0) :
    IsNonzeroMutualZeroDivisor
      (logicalWDWHamiltonian S t x y)
      (logicalWDWConjugate S t x y) := by
  refine ⟨hH, hHs, ?_, ?_⟩
  · rw [logicalWDWHamiltonian_mul_conjugate, hnull]
    simp
  · rw [logicalWDWConjugate_mul_hamiltonian, hnull]
    simp

#check logicalCodeUnit_idempotent
#check logicalCodeUnit_mul_logicalSigmaZ
#check logicalSigmaZ_mul_logicalCodeUnit
#check logicalCodeUnit_mul_logicalSigmaX
#check logicalSigmaX_mul_logicalCodeUnit
#check logicalSigmaZ_sq
#check logicalSigmaX_sq
#check logicalSigmaZ_anticommute_logicalSigmaX
#check logicalWDWHamiltonian_left_support
#check logicalWDWHamiltonian_right_support
#check logicalWDWConjugate_left_support
#check logicalWDWConjugate_right_support
#check logicalWDWHamiltonian_selfAdjoint
#check logicalWDWConjugate_selfAdjoint
#check logicalWDWHamiltonian_mul_conjugate
#check logicalWDWConjugate_mul_hamiltonian
#check logicalWDWHamiltonian_mul_conjugate_of_null
#check logicalWDWHamiltonian_inverse_in_corner
#check logicalWDW_null_gives_nonzeroMutualZeroDivisor

def logicalMatrixEmbedding (M : Matrix (Fin 2) (Fin 2) ℂ) : A :=
  M 0 0 • cuntzLogicalMatrixUnit S 0 0 +
  M 0 1 • cuntzLogicalMatrixUnit S 0 1 +
  M 1 0 • cuntzLogicalMatrixUnit S 1 0 +
  M 1 1 • cuntzLogicalMatrixUnit S 1 1

theorem logicalMatrixEmbedding_zero : logicalMatrixEmbedding S 0 = 0 := by
  unfold logicalMatrixEmbedding
  simp

def logicalWDWMatrix (t x y : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![(t + x : ℂ), (y : ℂ)], ![(y : ℂ), (t - x : ℂ)]]

def logicalWDWConjugateMatrix (t x y : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![(t - x : ℂ), -(y : ℂ)], ![-(y : ℂ), (t + x : ℂ)]]

theorem logicalWDWMatrix_eq_zero_iff (t x y : ℝ) :
    logicalWDWMatrix t x y = 0 ↔ t = 0 ∧ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h00 : (t + x : ℂ) = 0 := congrFun (congrFun h 0) 0
    have h01 : (y : ℂ) = 0 := congrFun (congrFun h 0) 1
    have h11 : (t - x : ℂ) = 0 := congrFun (congrFun h 1) 1
    have hy : y = 0 := by exact_mod_cast h01
    have ht : t = 0 := by
      have h1 : t + x = 0 := by exact_mod_cast h00
      have h2 : t - x = 0 := by exact_mod_cast h11
      linarith
    have hx : x = 0 := by
      have h1 : t + x = 0 := by exact_mod_cast h00
      have h2 : t - x = 0 := by exact_mod_cast h11
      linarith
    exact ⟨ht, hx, hy⟩
  · rintro ⟨rfl, rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [logicalWDWMatrix]

theorem logicalWDWConjugateMatrix_eq_zero_iff (t x y : ℝ) :
    logicalWDWConjugateMatrix t x y = 0 ↔ t = 0 ∧ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h00 : (t - x : ℂ) = 0 := congrFun (congrFun h 0) 0
    have h01 : -(y : ℂ) = 0 := congrFun (congrFun h 0) 1
    have h11 : (t + x : ℂ) = 0 := congrFun (congrFun h 1) 1
    have hy : y = 0 := by exact_mod_cast (neg_eq_zero.mp h01)
    have ht : t = 0 := by
      have h1 : t - x = 0 := by exact_mod_cast h00
      have h2 : t + x = 0 := by exact_mod_cast h11
      linarith
    have hx : x = 0 := by
      have h1 : t - x = 0 := by exact_mod_cast h00
      have h2 : t + x = 0 := by exact_mod_cast h11
      linarith
    exact ⟨ht, hx, hy⟩
  · rintro ⟨rfl, rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [logicalWDWConjugateMatrix]

theorem logicalWDWHamiltonian_eq_matrix_embedding (t x y : ℝ) :
    logicalWDWHamiltonian S t x y = logicalMatrixEmbedding S (logicalWDWMatrix t x y) := by
  unfold logicalWDWHamiltonian logicalMatrixEmbedding logicalWDWMatrix
    logicalCodeUnit logicalSigmaZ logicalSigmaX
  simp [logicalWDWHamiltonian, logicalMatrixEmbedding, logicalWDWMatrix,
    logicalCodeUnit, logicalSigmaZ, logicalSigmaX, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  have hreal (r : ℝ) (z : A) : r • z = (r : ℂ) • z := rfl
  simp_rw [hreal]
  module

theorem logicalWDWConjugate_eq_matrix_embedding (t x y : ℝ) :
    logicalWDWConjugate S t x y = logicalMatrixEmbedding S (logicalWDWConjugateMatrix t x y) := by
  unfold logicalWDWConjugate logicalMatrixEmbedding logicalWDWConjugateMatrix
    logicalCodeUnit logicalSigmaZ logicalSigmaX
  simp [logicalWDWConjugate, logicalMatrixEmbedding, logicalWDWConjugateMatrix,
    logicalCodeUnit, logicalSigmaZ, logicalSigmaX, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  have hreal (r : ℝ) (z : A) : r • z = (r : ℂ) • z := rfl
  simp_rw [hreal]
  module

theorem logicalWDWHamiltonian_ne_zero
    (t x y : ℝ)
    (h_inj : Function.Injective (logicalMatrixEmbedding S))
    (hnonzero : t ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0) :
    logicalWDWHamiltonian S t x y ≠ 0 := by
  intro hH
  have h1 : logicalMatrixEmbedding S (logicalWDWMatrix t x y) = logicalMatrixEmbedding S 0 := by
    rw [← logicalWDWHamiltonian_eq_matrix_embedding]
    rw [hH]
    exact logicalMatrixEmbedding_zero S |>.symm
  have h2 : logicalWDWMatrix t x y = 0 := h_inj h1
  have hxyz : ¬ (t = 0 ∧ x = 0 ∧ y = 0) := not_and_or.mpr (Or.imp_right not_and_or.mpr hnonzero)
  apply hxyz
  exact (logicalWDWMatrix_eq_zero_iff t x y).mp h2

theorem logicalWDWConjugate_ne_zero
    (t x y : ℝ)
    (h_inj : Function.Injective (logicalMatrixEmbedding S))
    (hnonzero : t ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0) :
    logicalWDWConjugate S t x y ≠ 0 := by
  intro hH
  have h1 : logicalMatrixEmbedding S (logicalWDWConjugateMatrix t x y) = logicalMatrixEmbedding S 0 := by
    rw [← logicalWDWConjugate_eq_matrix_embedding]
    rw [hH]
    exact logicalMatrixEmbedding_zero S |>.symm
  have h2 : logicalWDWConjugateMatrix t x y = 0 := h_inj h1
  have hxyz : ¬ (t = 0 ∧ x = 0 ∧ y = 0) := not_and_or.mpr (Or.imp_right not_and_or.mpr hnonzero)
  apply hxyz
  exact (logicalWDWConjugateMatrix_eq_zero_iff t x y).mp h2

theorem logicalWDWMatrix_det (t x y : ℝ) :
    Matrix.det (logicalWDWMatrix t x y) = (t^2 - x^2 - y^2 : ℂ) := by
  unfold logicalWDWMatrix
  rw [Matrix.det_fin_two]
  dsimp
  push_cast
  ring

theorem logicalWDWMatrix_null_iff_det_zero (t x y : ℝ) :
    t^2 - x^2 - y^2 = 0 ↔ Matrix.det (logicalWDWMatrix t x y) = 0 := by
  rw [logicalWDWMatrix_det]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem logicalWDW_nontrivial_zero_divisor_pair
    (t x y : ℝ)
    (h_inj : Function.Injective (logicalMatrixEmbedding S))
    (hnull : t ^ 2 - x ^ 2 - y ^ 2 = 0)
    (hnonzero : t ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0) :
    IsNonzeroMutualZeroDivisor
      (logicalWDWHamiltonian S t x y)
      (logicalWDWConjugate S t x y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact logicalWDWHamiltonian_ne_zero S t x y h_inj hnonzero
  · exact logicalWDWConjugate_ne_zero S t x y h_inj hnonzero
  · rw [logicalWDWHamiltonian_mul_conjugate, hnull]
    simp
  · rw [logicalWDWConjugate_mul_hamiltonian, hnull]
    simp

#check logicalWDWHamiltonian_eq_matrix_embedding
#check logicalWDWHamiltonian_ne_zero
#check logicalWDWMatrix_det
#check logicalWDWMatrix_null_iff_det_zero
#check logicalWDW_nontrivial_zero_divisor_pair

end LogicalWheelerDeWittHamiltonian
