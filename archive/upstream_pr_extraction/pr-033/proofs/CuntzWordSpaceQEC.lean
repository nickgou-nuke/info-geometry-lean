import Mathlib
import proofs.CuntzMatrixCorner
import proofs.FiniteMatrixKnillLaflamme
import proofs.PeirceTensorQEC

noncomputable section

set_option maxHeartbeats 800000

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
  rw [StarMul.star_mul]
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  have h_inner : ∀ p q : Fin 2, star (S p) * S q = if p = q then 1 else 0 := by
    intro p q
    fin_cases p <;> fin_cases q <;> simp [hC.isom₁, hC.isom₂, hC.ortho₁₂, hC.ortho₂₁]
  calc
    star (S i2) * star (S i1) * (S j1 * S j2) =
        star (S i2) * ((star (S i1) * S j1) * S j2) := by noncomm_ring
    _ = star (S i2) * ((if i1 = j1 then 1 else 0) * S j2) := by
      rw [h_inner]
    _ = if (i1, i2) = (j1, j2) then 1 else 0 := by
      by_cases h : i1 = j1
      · subst j1
        simp [h_inner]
      · simp [h]

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
    (M i j) •
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
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem cuntzWordTwoCornerMap_smul
    (c : ℂ) (M : Matrix WordTwoIndex WordTwoIndex ℂ) :
    cuntzWordTwoCornerMap S (c • M) =
      algebraMap ℂ A c * cuntzWordTwoCornerMap S M := by
  unfold cuntzWordTwoCornerMap
  simp [Matrix.smul_apply, smul_smul, Algebra.smul_def, Finset.mul_sum,
    mul_assoc]

theorem cuntzWordTwoCornerMap_one :
    cuntzWordTwoCornerMap S 1 = 1 := by
  dsimp [cuntzWordTwoCornerMap, Matrix.one_apply]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]
  dsimp [cuntzWordTwoMatrixUnit, cuntzWordTwo]
  simp only [StarMul.star_mul]
  have step1 : (S 0 * S 0 * (star (S 0) * star (S 0)) + S 0 * S 1 * (star (S 1) * star (S 0))) = S 0 * (S 0 * star (S 0) + S 1 * star (S 1)) * star (S 0) := by noncomm_ring
  rw [step1, hC.cuntz_sum, mul_one]
  have step2 : (S 1 * S 0 * (star (S 0) * star (S 1)) + S 1 * S 1 * (star (S 1) * star (S 1))) = S 1 * (S 0 * star (S 0) + S 1 * star (S 1)) * star (S 1) := by noncomm_ring
  rw [step2, hC.cuntz_sum, mul_one]
  exact hC.cuntz_sum

theorem cuntzWordTwoCornerMap_mul
    (M N : Matrix WordTwoIndex WordTwoIndex ℂ) :
    cuntzWordTwoCornerMap S (M * N) =
      cuntzWordTwoCornerMap S M * cuntzWordTwoCornerMap S N := by
  classical
  simp only [cuntzWordTwoCornerMap, Matrix.mul_apply]
  rw [Fintype.sum_mul_sum]
  simp_rw [Fintype.sum_mul_sum]
  simp_rw [Finset.sum_smul]
  simp_rw [smul_mul_smul]
  simp_rw [cuntzWordTwoMatrixUnit_mul S]
  simp
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]

theorem cuntzWordTwoCornerMap_conjTranspose
    (M : Matrix WordTwoIndex WordTwoIndex ℂ) :
    cuntzWordTwoCornerMap S Mᴴ =
      star (cuntzWordTwoCornerMap S M) := by
  dsimp [cuntzWordTwoCornerMap, Matrix.conjTranspose_apply]
  have h_star : ∀ i j, star (cuntzWordTwoMatrixUnit S i j) = cuntzWordTwoMatrixUnit S j i := by
    intro i j; dsimp [cuntzWordTwoMatrixUnit]; simp only [StarMul.star_mul, star_star]
  simp only [star_sum, star_smul, h_star, starRingEnd_apply]
  rw [Finset.sum_comm]

def cuntzPeirceCodeProjector : A :=
  cuntzWordTwoCornerMap S PeirceTensorQEC.peirceCodeProjector

def logicalMatrixUnit (a b : Fin 2) : A :=
  cuntzWordTwoCornerMap S
    (PeirceTensorQEC.fibonacciPeircePlusComplex ⊗ₖ
      Matrix.single a b 1)

theorem logicalMatrixUnit_mul
    (a b c d : Fin 2) :
    logicalMatrixUnit S a b *
        logicalMatrixUnit S c d =
      if b = c then logicalMatrixUnit S a d else 0 := by
  unfold logicalMatrixUnit
  rw [← cuntzWordTwoCornerMap_mul]
  have hsingle : ∀ p q r s : Fin 2,
      Matrix.single p q (1 : ℂ) * Matrix.single r s 1 =
        if q = r then Matrix.single p s 1 else 0 := by
    intro p q r s
    by_cases h : q = r
    · subst r
      ext i j
      fin_cases p <;> fin_cases q <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.single, Fin.sum_univ_two]
    · ext i j
      fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases s <;>
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.single, Fin.sum_univ_two, h]
  have h_kron := Matrix.mul_kronecker_mul
    PeirceTensorQEC.fibonacciPeircePlusComplex
      PeirceTensorQEC.fibonacciPeircePlusComplex
    (Matrix.single a b (1 : ℂ)) (Matrix.single c d (1 : ℂ))
  rw [← h_kron]
  rw [hsingle]
  -- Using exact PeirceTensorQEC idempotency
  have h_idem : PeirceTensorQEC.fibonacciPeircePlusComplex * PeirceTensorQEC.fibonacciPeircePlusComplex = PeirceTensorQEC.fibonacciPeircePlusComplex := by
    exact PeirceTensorQEC.fibonacciPeircePlusComplex_isOrthogonalProjection.2
  rw [h_idem]
  by_cases h : b = c
  · subst c
    simp [logicalMatrixUnit, Matrix.single, h_idem]
  · simp [logicalMatrixUnit, h, Matrix.single, Matrix.kronecker_zero, cuntzWordTwoCornerMap_zero]

theorem logicalMatrixUnit_star
    (a b : Fin 2) :
    star (logicalMatrixUnit S a b) =
      logicalMatrixUnit S b a := by
  unfold logicalMatrixUnit
  rw [← cuntzWordTwoCornerMap_conjTranspose]
  have h_star := Matrix.conjTranspose_kronecker PeirceTensorQEC.fibonacciPeircePlusComplex
    (Matrix.single a b (1 : ℂ))
  rw [h_star]
  have h_sa : PeirceTensorQEC.fibonacciPeircePlusComplexᴴ = PeirceTensorQEC.fibonacciPeircePlusComplex := by
    exact PeirceTensorQEC.fibonacciPeircePlusComplex_isOrthogonalProjection.1
  rw [h_sa]
  have h_std : (Matrix.single a b (1 : ℂ))ᴴ = Matrix.single b a 1 := by
    simpa using (Matrix.conjTranspose_single a b (1 : ℂ))
  rw [h_std]

theorem logicalMatrixUnit_diag_sum :
    logicalMatrixUnit S 0 0 +
        logicalMatrixUnit S 1 1 =
      cuntzPeirceCodeProjector S := by
  unfold logicalMatrixUnit cuntzPeirceCodeProjector
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
    (h_P : PeirceTensorQEC.fibonacciPeircePlusComplex ⊗ₖ Matrix.single a b (1 : ℂ) ≠ 0) :
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
    ∃ lambda_mat : ι → ι → ℂ,
      ∀ a b,
        cuntzPeirceCodeProjector S *
            star (cuntzWordTwoCornerMap S (E a)) *
            cuntzWordTwoCornerMap S (E b) *
            cuntzPeirceCodeProjector S =
          algebraMap ℂ A (lambda_mat a b) *
            cuntzPeirceCodeProjector S := by
  obtain ⟨lambda_mat, hkl⟩ := hKL
  refine ⟨lambda_mat, ?_⟩
  intro a b
  have hmap :=
    congrArg (cuntzWordTwoCornerMap S) (hkl a b)
  simpa only [
    cuntzPeirceCodeProjector,
    cuntzWordTwoCornerMap_mul,
    cuntzWordTwoCornerMap_conjTranspose,
    cuntzWordTwoCornerMap_smul
  ] using hmap

end CuntzWordSpaceQEC
