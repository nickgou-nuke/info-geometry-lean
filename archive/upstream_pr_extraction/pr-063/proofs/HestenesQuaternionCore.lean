import proofs.HestenesHermitianMatrixBridge
import Mathlib.Algebra.QuaternionBasis

noncomputable section
namespace HestenesQuaternionCore

open HestenesCl14
open HestenesPauliSheetBridge
open HestenesEvenPauliEquiv
open HestenesKreinMatrixBridge
open HestenesHermitianAdjoint
open HestenesHermitianMatrixBridge

abbrev EvenAlgebra := ClPlus14

def q₁ : EvenAlgebra := volumeEven * sigmaEven 0
def q₂ : EvenAlgebra := volumeEven * sigmaEven 1
def q₃ : EvenAlgebra := volumeEven * sigmaEven 2

theorem q₁_sq : q₁ * q₁ = -1 := by
  apply clPlusToPauli_injective
  simp [q₁, map_mul, pauli1, pauli2, pauli3, Matrix.mul_apply,
    Fin.sum_univ_two]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

theorem q₂_sq : q₂ * q₂ = -1 := by
  apply clPlusToPauli_injective
  simp [q₂, map_mul, pauli1, pauli2, pauli3, Matrix.mul_apply,
    Fin.sum_univ_two]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

theorem q₃_sq : q₃ * q₃ = -1 := by
  apply clPlusToPauli_injective
  simp [q₃, map_mul, pauli1, pauli2, pauli3, Matrix.mul_apply,
    Fin.sum_univ_two]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

theorem q₁_mul_q₂ : q₁ * q₂ = -q₃ := by
  apply clPlusToPauli_injective
  simp [q₁, q₂, q₃, map_mul, pauli1, pauli2, pauli3,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem q₂_mul_q₃ : q₂ * q₃ = -q₁ := by
  apply clPlusToPauli_injective
  simp [q₁, q₂, q₃, map_mul, pauli1, pauli2, pauli3,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem q₃_mul_q₁ : q₃ * q₁ = -q₂ := by
  apply clPlusToPauli_injective
  simp [q₁, q₂, q₃, map_mul, pauli1, pauli2, pauli3,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem q₂_mul_q₁ : q₂ * q₁ = q₃ := by
  apply clPlusToPauli_injective
  simp [q₁, q₂, q₃, map_mul, pauli1, pauli2, pauli3,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- Quaternion basis inside the even spacetime algebra.  The third unit is
`-q₃` because the orientation already fixed by `volumeEven` gives
`q₁ q₂ = -q₃`. -/
def rotationQuaternionBasis :
    QuaternionAlgebra.Basis EvenAlgebra (-1 : ℝ) 0 (-1 : ℝ) where
  i := q₁
  j := q₂
  k := -q₃
  i_mul_i := by rw [q₁_sq]; simp
  j_mul_j := by rw [q₂_sq]; simp
  i_mul_j := q₁_mul_q₂
  j_mul_i := by rw [q₂_mul_q₁]; simp

abbrev HRot := Quaternion ℝ

/-- Native algebra embedding of the quaternion rotation algebra into
`Cl⁺(1,3)`. -/
def hRotToEven : HRot →ₐ[ℝ] EvenAlgebra :=
  QuaternionAlgebra.Basis.liftHom rotationQuaternionBasis

@[simp] theorem adjoint_q₁ : hestenesAdjoint q₁ = -q₁ := by
  apply clPlusToPauli_injective
  rw [clPlusToPauli_hestenesAdjoint]
  simp [q₁, map_mul, pauli1, pauli2, pauli3,
    Matrix.conjTranspose_apply]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

@[simp] theorem adjoint_q₂ : hestenesAdjoint q₂ = -q₂ := by
  apply clPlusToPauli_injective
  rw [clPlusToPauli_hestenesAdjoint]
  simp [q₂, map_mul, pauli1, pauli2, pauli3,
    Matrix.conjTranspose_apply]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

@[simp] theorem adjoint_q₃ : hestenesAdjoint q₃ = -q₃ := by
  apply clPlusToPauli_injective
  rw [clPlusToPauli_hestenesAdjoint]
  simp [q₃, map_mul, pauli1, pauli2, pauli3,
    Matrix.conjTranspose_apply]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

end HestenesQuaternionCore
end noncomputable section
