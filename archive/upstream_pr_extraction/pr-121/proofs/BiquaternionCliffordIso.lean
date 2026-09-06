import Mathlib

open Matrix Complex

/-!
# Biquaternion–Pauli/Clifford realization

Formal verification of the standard matrix realization
`ℍ_ℂ ≅ Cl_{3,0}(ℝ) ⊗ ℂ ≅ M₂(ℂ)` via Pauli matrices.  We verify the
matrix identities that implement the Clifford generators, the quaternionic even
subalgebra, the central pseudoscalar, Pauli-basis spanning, and determinant norm.
-/

noncomputable section

namespace BiquaternionCliffordIso

/-- Pauli σ₁. -/
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli σ₂. -/
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Pauli σ₃. -/
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

lemma σ₁_sq : σ₁ * σ₁ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ₁, Matrix.mul_apply, Fin.sum_univ_two]

lemma σ₂_sq : σ₂ * σ₂ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ₂, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

lemma σ₃_sq : σ₃ * σ₃ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ₃, Matrix.mul_apply, Fin.sum_univ_two]

lemma σ₁σ₂_anti : σ₁ * σ₂ = -(σ₂ * σ₁) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₂, Matrix.mul_apply, Fin.sum_univ_two]

lemma σ₁σ₃_anti : σ₁ * σ₃ = -(σ₃ * σ₁) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₃, Matrix.mul_apply, Fin.sum_univ_two]

lemma σ₂σ₃_anti : σ₂ * σ₃ = -(σ₃ * σ₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]

/-- Quaternion unit i as a reversed Pauli bivector. -/
def i_q : Matrix (Fin 2) (Fin 2) ℂ := σ₃ * σ₂

/-- Quaternion unit j as a reversed Pauli bivector. -/
def j_q : Matrix (Fin 2) (Fin 2) ℂ := σ₁ * σ₃

/-- Quaternion unit k as a reversed Pauli bivector. -/
def k_q : Matrix (Fin 2) (Fin 2) ℂ := σ₂ * σ₁

lemma i_q_sq : i_q * i_q = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [i_q, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

lemma j_q_sq : j_q * j_q = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [j_q, σ₁, σ₃, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

lemma k_q_sq : k_q * k_q = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k_q, σ₁, σ₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

lemma ij_eq_k : i_q * j_q = k_q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [i_q, j_q, k_q, σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]

lemma ijk_eq_neg_one : i_q * j_q * k_q = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [i_q, j_q, k_q, σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/-- Pseudoscalar ω = σ₁σ₂σ₃. -/
def ω : Matrix (Fin 2) (Fin 2) ℂ := σ₁ * σ₂ * σ₃

lemma ω_eq_iI : ω = I • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ω, σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

lemma ω_sq : ω * ω = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ω, σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

lemma ω_comm_σ₁ : ω * σ₁ = σ₁ * ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ω, σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]

lemma ω_comm_σ₂ : ω * σ₂ = σ₂ * ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ω, σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]

lemma ω_comm_σ₃ : ω * σ₃ = σ₃ * ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ω, σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]

/-- Every 2×2 complex matrix decomposes in the Pauli basis. -/
theorem M2C_pauli_decompose (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = ((M 0 0 + M 1 1) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((M 0 1 + M 1 0) / 2) • σ₁ +
        ((I * (M 0 1 - M 1 0)) / 2) • σ₂ +
        ((M 0 0 - M 1 1) / 2) • σ₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₂, σ₃, Matrix.smul_apply, Matrix.add_apply] <;>
    ring_nf
  all_goals
    simp [pow_two, Complex.I_mul_I]
    ring_nf

/-- Determinant of a Pauli expansion. -/
theorem pauli_det (α x y z : ℂ) :
    Matrix.det (α • (1 : Matrix (Fin 2) (Fin 2) ℂ) + x • σ₁ + y • σ₂ + z • σ₃) =
    α * α - x * x - y * y - z * z := by
  simp [Matrix.det_fin_two, σ₁, σ₂, σ₃, Matrix.smul_apply, Matrix.add_apply]
  ring_nf
  simp [pow_two, Complex.I_mul_I]
  ring_nf

#check M2C_pauli_decompose
#check pauli_det

end BiquaternionCliffordIso
