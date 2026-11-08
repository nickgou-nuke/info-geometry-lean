import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace JordanBlock2

open Matrix

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev V2C := InfoGeometry.Algebra.FiniteSpin.Vec2C

/-- Matrix-vector action. -/
def matVec (A : M2C) (v : V2C) : V2C :=
  fun i => ∑ j : Fin 2, A i j * v j

/-- First coordinate vector. -/
def e0 : V2C
  | 0 => 1
  | 1 => 0

/-- Second coordinate vector. -/
def e1 : V2C
  | 0 => 0
  | 1 => 1

/-- The nilpotent part of a 2×2 Jordan block. -/
def N2 : M2C := !![0, 1; 0, 0]

/-- The 2×2 Jordan block with eigenvalue `λ`. -/
def J2 (lam : ℂ) : M2C := !![lam, 1; 0, lam]

@[simp] theorem N2_sq : N2 * N2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [N2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The nilpotent part commutes with the Jordan block on the right. -/
theorem N2_mul_J2 (lam : ℂ) : N2 * J2 lam = lam • N2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2, N2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The nilpotent part commutes with the Jordan block on the left. -/
theorem J2_mul_N2 (lam : ℂ) : J2 lam * N2 = lam • N2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2, N2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The nilpotent sends the generalized eigenvector `e₁` to eigenvector `e₀`. -/
theorem N2_apply_e1 : matVec N2 e1 = e0 := by
  funext i
  fin_cases i <;> simp [matVec, N2, e0, e1, Fin.sum_univ_two]

/-- The nilpotent kills the eigenvector `e₀`. -/
theorem N2_apply_e0 : matVec N2 e0 = 0 := by
  funext i
  fin_cases i <;> simp [matVec, N2, e0, Fin.sum_univ_two]

/-- The nilpotent kernel is one-dimensional in coordinates: `Nv=0` iff `v₁=0`. -/
theorem N2_kernel_iff (v : V2C) : matVec N2 v = 0 ↔ v 1 = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa [matVec, N2, Fin.sum_univ_two] using h0
  · intro hv
    funext i
    fin_cases i <;> simp [matVec, N2, Fin.sum_univ_two, hv]

/-- The nilpotent part is nonzero, so the block is genuinely non-diagonal. -/
theorem N2_ne_zero : N2 ≠ 0 := by
  intro h
  have hij := congrArg (fun A : M2C => A 0 1) h
  norm_num [N2] at hij

/-- Jordan block splits as scalar plus nilpotent part. -/
theorem J2_eq_scalar_add_nilpotent (lam : ℂ) :
    J2 lam = lam • (1 : M2C) + N2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2, N2]

/-- The ordinary eigenvector relation for the first vector in the chain. -/
theorem J2_apply_e0 (lam : ℂ) : matVec (J2 lam) e0 = lam • e0 := by
  funext i
  fin_cases i <;> simp [matVec, J2, e0, Fin.sum_univ_two]

/-- The generalized eigenvector relation for the second vector in the chain. -/
theorem J2_apply_e1 (lam : ℂ) : matVec (J2 lam) e1 = lam • e1 + e0 := by
  funext i
  fin_cases i <;> simp [matVec, J2, e0, e1, Fin.sum_univ_two]

/-- Square of a 2×2 Jordan block: the first nontrivial power formula. -/
theorem J2_sq (lam : ℂ) :
    J2 lam * J2 lam = (lam ^ 2) • (1 : M2C) + (2 * lam) • N2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2, N2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- AFP-style power formula for this single Jordan block.  This is not a general
Jordan normal form theorem; it is the verified local block calculation. -/
theorem J2_power_succ (lam : ℂ) (n : ℕ) :
    (J2 lam) ^ (n + 1) =
      (lam ^ (n + 1)) • (1 : M2C) + (((n + 1 : ℕ) : ℂ) * lam ^ n) • N2 := by
  induction n with
  | zero =>
      simp [J2_eq_scalar_add_nilpotent, one_smul]
  | succ n ih =>
      calc
        (J2 lam) ^ (n.succ + 1) = (J2 lam) ^ (n + 1) * J2 lam := by
          rw [pow_succ]
        _ = ((lam ^ (n + 1)) • (1 : M2C) +
              ((((n + 1 : ℕ) : ℂ) * lam ^ n) • N2)) * J2 lam := by
              rw [ih]
        _ = (lam ^ (n + 2)) • (1 : M2C) +
              ((((n + 2 : ℕ) : ℂ) * lam ^ (n + 1)) • N2) := by
              ext i j
              fin_cases i <;> fin_cases j <;>
                simp [J2, N2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Removing the eigenvalue leaves the square-zero Jordan nilpotent. -/
theorem J2_nilpotent_part_sq (lam : ℂ) :
    (J2 lam - lam • (1 : M2C)) * (J2 lam - lam • (1 : M2C)) = 0 := by
  rw [J2_eq_scalar_add_nilpotent]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [N2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The determinant of a 2×2 Jordan block is `λ²`. -/
theorem det_J2 (lam : ℂ) : (J2 lam).det = lam ^ 2 := by
  simp [J2, Matrix.det_fin_two]
  ring

/-- The trace of a 2×2 Jordan block is `2λ`. -/
theorem trace_J2 (lam : ℂ) : Matrix.trace (J2 lam) = 2 * lam := by
  simp [J2, Matrix.trace, Fin.sum_univ_two]
  ring

/-- The characteristic polynomial data encoded by trace and determinant. -/
theorem J2_trace_det_package (lam : ℂ) :
    Matrix.trace (J2 lam) = 2 * lam ∧ (J2 lam).det = lam ^ 2 ∧
    (J2 lam - lam • (1 : M2C)) * (J2 lam - lam • (1 : M2C)) = 0 ∧
    J2 lam - lam • (1 : M2C) ≠ 0 := by
  refine ⟨trace_J2 lam, det_J2 lam, J2_nilpotent_part_sq lam, ?_⟩
  intro h
  have hN : N2 = 0 := by
    rw [J2_eq_scalar_add_nilpotent] at h
    simpa using h
  exact N2_ne_zero hN

#check N2_sq
#check N2_mul_J2
#check J2_mul_N2
#check N2_apply_e1
#check N2_apply_e0
#check N2_kernel_iff
#check N2_ne_zero
#check J2_apply_e0
#check J2_apply_e1
#check J2_sq
#check J2_power_succ
#check J2_nilpotent_part_sq
#check det_J2
#check trace_J2
#check J2_trace_det_package

end JordanBlock2
