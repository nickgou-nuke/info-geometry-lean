import InfoGeometry.Canonical.BiquaternionNegativeRootsLog

open Matrix Complex

/-!
# Biquaternion–Pauli/Clifford property

Maintained owner for the finite Pauli/Clifford property recovered from the
external-auto and removable-disk lanes. It reuses the canonical Pauli matrices
already restored in `BiquaternionNegativeRootsLog` and packages the explicit
matrix identities implementing the `M₂(ℂ)` realization.
-/

noncomputable section

namespace InfoGeometry.Canonical.BiquaternionCliffordIso

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

def σ₁ : M2C := BiquaternionNegativeRootsLog.σ₁
def σ₂ : M2C := BiquaternionNegativeRootsLog.σ₂
def σ₃ : M2C := BiquaternionNegativeRootsLog.σ₃

lemma σ₁_sq : σ₁ * σ₁ = (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₁, BiquaternionNegativeRootsLog.σ₁, Matrix.mul_apply, Fin.sum_univ_two]

lemma σ₂_sq : σ₂ * σ₂ = (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₂, BiquaternionNegativeRootsLog.σ₂, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.I_mul_I]

lemma σ₃_sq : σ₃ * σ₃ = (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₃, BiquaternionNegativeRootsLog.σ₃, Matrix.mul_apply, Fin.sum_univ_two]

lemma σ₁σ₂_anti : σ₁ * σ₂ = -(σ₂ * σ₁) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₂, BiquaternionNegativeRootsLog.σ₁,
      BiquaternionNegativeRootsLog.σ₂,
      Matrix.mul_apply, Fin.sum_univ_two]

lemma σ₁σ₃_anti : σ₁ * σ₃ = -(σ₃ * σ₁) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₃, BiquaternionNegativeRootsLog.σ₁,
      BiquaternionNegativeRootsLog.σ₃,
      Matrix.mul_apply, Fin.sum_univ_two]

lemma σ₂σ₃_anti : σ₂ * σ₃ = -(σ₃ * σ₂) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₂, σ₃, BiquaternionNegativeRootsLog.σ₂,
      BiquaternionNegativeRootsLog.σ₃,
      Matrix.mul_apply, Fin.sum_univ_two]

def i_q : M2C := σ₃ * σ₂
def j_q : M2C := σ₁ * σ₃
def k_q : M2C := σ₂ * σ₁

lemma i_q_sq : i_q * i_q = -(1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [i_q, σ₂, σ₃, BiquaternionNegativeRootsLog.σ₂,
      BiquaternionNegativeRootsLog.σ₃,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

lemma j_q_sq : j_q * j_q = -(1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [j_q, σ₁, σ₃, BiquaternionNegativeRootsLog.σ₁,
      BiquaternionNegativeRootsLog.σ₃,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

lemma k_q_sq : k_q * k_q = -(1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [k_q, σ₁, σ₂, BiquaternionNegativeRootsLog.σ₁,
      BiquaternionNegativeRootsLog.σ₂,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

lemma ij_eq_k : i_q * j_q = k_q := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [i_q, j_q, k_q, σ₁, σ₂, σ₃,
      BiquaternionNegativeRootsLog.σ₁,
      BiquaternionNegativeRootsLog.σ₂,
      BiquaternionNegativeRootsLog.σ₃,
      Matrix.mul_apply, Fin.sum_univ_two]

lemma ijk_eq_neg_one : i_q * j_q * k_q = -(1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [i_q, j_q, k_q, σ₁, σ₂, σ₃,
      BiquaternionNegativeRootsLog.σ₁,
      BiquaternionNegativeRootsLog.σ₂,
      BiquaternionNegativeRootsLog.σ₃,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

def ω : M2C := σ₁ * σ₂ * σ₃

lemma ω_eq_iI : ω = I • (1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [ω, σ₁, σ₂, σ₃,
      BiquaternionNegativeRootsLog.σ₁,
      BiquaternionNegativeRootsLog.σ₂,
      BiquaternionNegativeRootsLog.σ₃,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

lemma ω_sq : ω * ω = -(1 : M2C) := by
  rw [ω_eq_iI]
  simpa using BiquaternionNegativeRootsLog.scalar_i_square_root_neg_one

lemma ω_comm_σ₁ : ω * σ₁ = σ₁ * ω := by
  rw [ω_eq_iI]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₁, BiquaternionNegativeRootsLog.σ₁,
      Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]

lemma ω_comm_σ₂ : ω * σ₂ = σ₂ * ω := by
  rw [ω_eq_iI]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₂, BiquaternionNegativeRootsLog.σ₂,
      Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]

lemma ω_comm_σ₃ : ω * σ₃ = σ₃ * ω := by
  rw [ω_eq_iI]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₃, BiquaternionNegativeRootsLog.σ₃,
      Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]

theorem M2C_pauli_decompose (M : M2C) :
    M = ((M 0 0 + M 1 1) / 2) • (1 : M2C) +
        ((M 0 1 + M 1 0) / 2) • σ₁ +
        ((I * (M 0 1 - M 1 0)) / 2) • σ₂ +
        ((M 0 0 - M 1 1) / 2) • σ₃ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [σ₁, σ₂, σ₃,
      BiquaternionNegativeRootsLog.σ₁,
      BiquaternionNegativeRootsLog.σ₂,
      BiquaternionNegativeRootsLog.σ₃,
      Matrix.smul_apply, Matrix.add_apply] <;>
    (ring_nf; try simp [Complex.I_mul_I]; try ring)

theorem pauli_det (α x y z : ℂ) :
    Matrix.det (α • (1 : M2C) + x • σ₁ + y • σ₂ + z • σ₃) =
    α * α - x * x - y * y - z * z := by
  simp [σ₁, σ₂, σ₃,
    BiquaternionNegativeRootsLog.σ₁,
    BiquaternionNegativeRootsLog.σ₂,
    BiquaternionNegativeRootsLog.σ₃,
    Matrix.det_fin_two, Matrix.smul_apply, Matrix.add_apply]
  ring_nf
  simp [Complex.I_mul_I]
  ring

end InfoGeometry.Canonical.BiquaternionCliffordIso
