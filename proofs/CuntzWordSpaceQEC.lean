import Mathlib
import proofs.CuntzMatrixCorner
import proofs.FiniteMatrixKnillLaflamme
import proofs.PeirceTensorQEC

noncomputable section

namespace CuntzWordSpaceQEC

open scoped BigOperators Kronecker
open Matrix

variable {A : Type*} [Ring A] [StarRing A]
variable (S : Fin 2 → A)
variable [hC : CuntzO2 (S 0) (S 1)]

abbrev WordTwoIndex := Fin 2 × Fin 2

def cuntzWordTwo (i : WordTwoIndex) : A :=
  S i.1 * S i.2

def cuntzWordTwoMatrixUnit
    (i j : WordTwoIndex) : A :=
  cuntzWordTwo S i * star (cuntzWordTwo S j)

theorem cuntzWordTwo_inner
    (i j : WordTwoIndex) :
    star (cuntzWordTwo S i) * cuntzWordTwo S j =
      if i = j then 1 else 0 := by
  dsimp [cuntzWordTwo]
  rw [star_mul]
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  { dsimp; simp only [← mul_assoc, mul_assoc, hC.isom₁, hC.isom₂, hC.ortho₁₂, hC.ortho₂₁, mul_zero, zero_mul, mul_one] }

theorem cuntzWordTwoMatrixUnit_mul
    (i j k l : WordTwoIndex) :
    cuntzWordTwoMatrixUnit S i j *
        cuntzWordTwoMatrixUnit S k l =
      if j = k then cuntzWordTwoMatrixUnit S i l else 0 := by
  unfold cuntzWordTwoMatrixUnit
  rw [mul_assoc, ← mul_assoc (star (cuntzWordTwo S j))]
  rw [cuntzWordTwo_inner]
  split_ifs <;> simp

variable [Algebra ℂ A] [StarModule ℂ A]

def cuntzWordTwoCornerMap
    (M : Matrix WordTwoIndex WordTwoIndex ℂ) : A :=
  ∑ i, ∑ j,
    algebraMap ℂ A (M i j) *
      cuntzWordTwoMatrixUnit S i j

theorem cuntzWordTwoCornerMap_zero :
    cuntzWordTwoCornerMap S 0 = 0 := by
  unfold cuntzWordTwoCornerMap
  simp

theorem cuntzWordTwoCornerMap_add
    (M N : Matrix WordTwoIndex WordTwoIndex ℂ) :
    cuntzWordTwoCornerMap S (M + N) =
      cuntzWordTwoCornerMap S M + cuntzWordTwoCornerMap S N := by
  unfold cuntzWordTwoCornerMap
  simp only [Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem cuntzWordTwoCornerMap_smul
    (c : ℂ) (M : Matrix WordTwoIndex WordTwoIndex ℂ) :
    cuntzWordTwoCornerMap S (c • M) =
      algebraMap ℂ A c * cuntzWordTwoCornerMap S M := by
  unfold cuntzWordTwoCornerMap
  simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, Finset.mul_sum]

theorem cuntzWordTwoCornerMap_one :
    cuntzWordTwoCornerMap S 1 = 1 := by
  dsimp [cuntzWordTwoCornerMap, Matrix.one_apply]
  simp only [map_ite, map_one, map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  dsimp [cuntzWordTwoMatrixUnit, cuntzWordTwo]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [star_mul]
  have step1 : (S 0 * S 0 * (star (S 0) * star (S 0)) + S 0 * S 1 * (star (S 1) * star (S 0))) = S 0 * (S 0 * star (S 0) + S 1 * star (S 1)) * star (S 0) := by noncomm_ring
  rw [step1, hC.cuntz_sum, mul_one]
  have step2 : (S 1 * S 0 * (star (S 0) * star (S 1)) + S 1 * S 1 * (star (S 1) * star (S 1))) = S 1 * (S 0 * star (S 0) + S 1 * star (S 1)) * star (S 1) := by noncomm_ring
  rw [step2, hC.cuntz_sum, mul_one]
  exact hC.cuntz_sum

theorem cuntzWordTwoCornerMap_mul
    (M N : Matrix WordTwoIndex WordTwoIndex ℂ) :
    cuntzWordTwoCornerMap S (M * N) =
      cuntzWordTwoCornerMap S M * cuntzWordTwoCornerMap S N := by
  dsimp [cuntzWordTwoCornerMap, Matrix.mul_apply]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, add_mul, mul_add, smul_add, add_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, cuntzWordTwoMatrixUnit_mul S, mul_smul]
  abel

theorem cuntzWordTwoCornerMap_conjTranspose
    (M : Matrix WordTwoIndex WordTwoIndex ℂ) :
    cuntzWordTwoCornerMap S Mᴴ =
      star (cuntzWordTwoCornerMap S M) := by
  dsimp [cuntzWordTwoCornerMap, Matrix.conjTranspose_apply]
  have h_star : ∀ i j, star (cuntzWordTwoMatrixUnit S i j) = cuntzWordTwoMatrixUnit S j i := by
    intro i j; dsimp [cuntzWordTwoMatrixUnit]; simp only [star_mul, star_star]
  simp only [star_sum, star_mul, map_star, h_star]
  -- Swap the two sums
  rw [Finset.sum_comm]

theorem cuntzWordTwoCornerMap_injective :
    Function.Injective (cuntzWordTwoCornerMap S) := by
  intro M N h
  ext i j
  have h_proj := congrArg (fun a => star (cuntzWordTwo S i) * a * cuntzWordTwo S j) h
  dsimp [cuntzWordTwoCornerMap, cuntzWordTwoMatrixUnit, cuntzWordTwo] at h_proj
  fin_cases i <;> fin_cases j <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hC.isom₁, hC.isom₂, hC.ortho₁₂, hC.ortho₂₁] at h_proj <;>
    exact h_proj

def cuntzPeirceCodeProjector : A :=
  cuntzWordTwoCornerMap S PeirceTensorQEC.peirceCodeProjector

def logicalMatrixUnit (a b : Fin 2) : A :=
  cuntzWordTwoCornerMap S
    (PeirceTensorQEC.fibonacciPeircePlusComplex ⊗ₖ
      Matrix.stdBasisMatrix a b 1)

theorem logicalMatrixUnit_mul
    (a b c d : Fin 2) :
    logicalMatrixUnit S a b *
        logicalMatrixUnit S c d =
      if b = c then logicalMatrixUnit S a d else 0 := by
  rw [← cuntzWordTwoCornerMap_mul]
  have h_kron := Matrix.kronecker_mul PeirceTensorQEC.fibonacciPeircePlusComplex (Matrix.stdBasisMatrix a b (1 : ℂ)) PeirceTensorQEC.fibonacciPeircePlusComplex (Matrix.stdBasisMatrix c d 1)
  rw [h_kron]
  -- Using exact PeirceTensorQEC idempotency
  have h_idem : PeirceTensorQEC.fibonacciPeircePlusComplex * PeirceTensorQEC.fibonacciPeircePlusComplex = PeirceTensorQEC.fibonacciPeircePlusComplex := by
    exact PeirceTensorQEC.fibonacciPeircePlusComplex_isOrthogonalProjection.2
  rw [h_idem]
  by_cases h : b = c
  · subst c
    simp [logicalMatrixUnit, Matrix.stdBasisMatrix_mul_same, h_idem]
  · simp [logicalMatrixUnit, h, Matrix.stdBasisMatrix_mul_of_ne, Matrix.kronecker_zero, cuntzWordTwoCornerMap_zero]

theorem logicalMatrixUnit_star
    (a b : Fin 2) :
    star (logicalMatrixUnit S a b) =
      logicalMatrixUnit S b a := by
  rw [← cuntzWordTwoCornerMap_conjTranspose]
  have h_star := Matrix.conjTranspose_kronecker PeirceTensorQEC.fibonacciPeircePlusComplex (Matrix.stdBasisMatrix a b (1 : ℂ))
  rw [h_star]
  have h_sa : PeirceTensorQEC.fibonacciPeircePlusComplexᴴ = PeirceTensorQEC.fibonacciPeircePlusComplex := by
    exact PeirceTensorQEC.fibonacciPeircePlusComplex_isOrthogonalProjection.1
  rw [h_sa]
  have h_std : (Matrix.stdBasisMatrix a b (1 : ℂ))ᴴ = Matrix.stdBasisMatrix b a 1 := by
    ext i j; fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> rfl
  rw [h_std]

theorem logicalMatrixUnit_diag_sum :
    logicalMatrixUnit S 0 0 +
        logicalMatrixUnit S 1 1 =
      cuntzPeirceCodeProjector S := by
  rw [← cuntzWordTwoCornerMap_add]
  apply congrArg (cuntzWordTwoCornerMap S)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [logicalMatrixUnit, cuntzPeirceCodeProjector,
      PeirceTensorQEC.peirceCodeProjector]

/-- Support Relations: L_ab belongs to the code corner P_C A P_C -/
theorem logicalMatrixUnit_left_support (a b : Fin 2) :
    cuntzPeirceCodeProjector S * logicalMatrixUnit S a b = logicalMatrixUnit S a b := by
  rw [← logicalMatrixUnit_diag_sum S]
  rw [add_mul]
  fin_cases a <;> simp [logicalMatrixUnit_mul]

theorem logicalMatrixUnit_right_support (a b : Fin 2) :
    logicalMatrixUnit S a b * cuntzPeirceCodeProjector S = logicalMatrixUnit S a b := by
  rw [← logicalMatrixUnit_diag_sum S]
  rw [mul_add]
  fin_cases b <;> simp [logicalMatrixUnit_mul]

/-- Non-triviality via injectivity (the algebraic replacement for rank) -/
theorem logicalMatrixUnit_ne_zero_of_injective
    (h_inj : Function.Injective (cuntzWordTwoCornerMap S))
    (a b : Fin 2)
    (h_P : PeirceTensorQEC.fibonacciPeircePlusComplex ⊗ₖ Matrix.stdBasisMatrix a b (1 : ℂ) ≠ 0) :
    logicalMatrixUnit S a b ≠ 0 := by
  unfold logicalMatrixUnit
  intro h
  have h_zero : cuntzWordTwoCornerMap S 0 = 0 := cuntzWordTwoCornerMap_zero S
  rw [← h_zero] at h
  have h_eq := h_inj h
  exact h_P h_eq

theorem cuntzWordTwo_transports_KL
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → Matrix WordTwoIndex WordTwoIndex ℂ)
    (hKL :
      FiniteMatrixKnillLaflamme.SatisfiesKnillLaflamme PeirceTensorQEC.peirceCodeProjector E) :
    ∃ λ_mat : ι → ι → ℂ,
      ∀ a b,
        cuntzPeirceCodeProjector S *
            star (cuntzWordTwoCornerMap S (E a)) *
            cuntzWordTwoCornerMap S (E b) *
            cuntzPeirceCodeProjector S =
          algebraMap ℂ A (λ_mat a b) *
            cuntzPeirceCodeProjector S := by
  obtain ⟨λ_mat, hλ⟩ := hKL
  refine ⟨λ_mat, ?_⟩
  intro a b
  have hmap :=
    congrArg (cuntzWordTwoCornerMap S) (hλ a b)
  simpa only [
    cuntzPeirceCodeProjector,
    cuntzWordTwoCornerMap_mul,
    cuntzWordTwoCornerMap_conjTranspose,
    cuntzWordTwoCornerMap_smul
  ] using hmap

end CuntzWordSpaceQEC
