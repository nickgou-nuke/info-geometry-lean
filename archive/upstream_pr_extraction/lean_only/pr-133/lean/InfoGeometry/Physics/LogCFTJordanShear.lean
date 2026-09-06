import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic
import InfoGeometry.Clifford.NilpotentBinomial

/-!
# Finite logarithmic-Jordan shear

This owner isolates the exact finite-dimensional algebra behind a rank-two
logarithmic Jordan block.  It proves the nilpotent square and records the
phase times unipotent-shear factorization.  No analytic monodromy or de Rham
cohomology statement is asserted here.
-/

namespace InfoGeometry.Physics.LogCFTJordanShear

noncomputable section

abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

def nilpotentN : Mat2C := !![0, 1; 0, 0]

theorem nilpotentN_sq_zero : nilpotentN * nilpotentN = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nilpotentN, Matrix.mul_apply]

theorem nilpotentN_pow_add_two (n : ℕ) :
    nilpotentN ^ (n + 2) = 0 := by
  induction n with
  | zero => simpa [pow_two] using nilpotentN_sq_zero
  | succ n ih =>
      rw [Nat.succ_add, pow_succ, ih, zero_mul]

theorem scaledNilpotent_pow_add_two (τ : ℂ) (n : ℕ) :
    (τ • nilpotentN) ^ (n + 2) = 0 := by
  induction n with
  | zero =>
      simp [pow_two, nilpotentN_sq_zero]
  | succ n ih =>
      rw [Nat.succ_add, pow_succ, ih, zero_mul]

theorem exp_scaledNilpotent (τ : ℂ) :
    NormedSpace.exp (τ • nilpotentN) = (1 : Mat2C) + τ • nilpotentN := by
  rw [NormedSpace.exp_eq_tsum_rat]
  change (∑' n : ℕ, (n.factorial : ℚ)⁻¹ • (τ • nilpotentN) ^ n) =
    (1 : Mat2C) + τ • nilpotentN
  rw [tsum_eq_sum (s := {0, 1})]
  · simp
  · intro n hn
    have hn0 : n ≠ 0 := by
      intro h
      apply hn
      simp [h]
    have hn1 : n ≠ 1 := by
      intro h
      apply hn
      simp [h]
    have htwo : 2 ≤ n := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htwo
    have hpow : (τ • nilpotentN) ^ (2 + k) = 0 := by
      simpa [Nat.add_comm] using (scaledNilpotent_pow_add_two τ k)
    rw [hpow]
    simp

def unipotentShear (τ : ℂ) : Mat2C :=
  (1 : Mat2C) + τ • nilpotentN

def jordanHamiltonian (δ : ℂ) : Mat2C :=
  δ • (1 : Mat2C) + nilpotentN

theorem exp_scalar_identity (δ : ℂ) :
    NormedSpace.exp (δ • (1 : Mat2C)) = Complex.exp δ • (1 : Mat2C) := by
  have hdiag : δ • (1 : Mat2C) = Matrix.diagonal (fun _ : Fin 2 => δ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hdiag, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← Complex.exp_eq_exp_ℂ]

theorem exp_jordanHamiltonian (δ : ℂ) :
    NormedSpace.exp (jordanHamiltonian δ) =
      Complex.exp δ • unipotentShear 1 := by
  have hcomm : Commute (δ • (1 : Mat2C)) nilpotentN := by
    rw [Commute]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hN : NormedSpace.exp nilpotentN = unipotentShear 1 := by
    simpa [unipotentShear] using (exp_scaledNilpotent (1 : ℂ))
  unfold jordanHamiltonian
  rw [Matrix.exp_add_of_commute _ _ hcomm, exp_scalar_identity, hN]
  unfold unipotentShear
  simp [smul_add]

theorem exp_smul_jordanHamiltonian (a δ : ℂ) :
    NormedSpace.exp (a • jordanHamiltonian δ) =
      Complex.exp (a * δ) • unipotentShear a := by
  have hcomm : Commute ((a * δ) • (1 : Mat2C)) (a • nilpotentN) := by
    rw [Commute]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have hrewrite : a • jordanHamiltonian δ =
      (a * δ) • (1 : Mat2C) + a • nilpotentN := by
    unfold jordanHamiltonian
    rw [smul_add, smul_smul]
  rw [hrewrite, Matrix.exp_add_of_commute _ _ hcomm,
    exp_scalar_identity, exp_scaledNilpotent]
  unfold unipotentShear
  simp [smul_add, smul_smul, mul_comm, add_comm]

def logCFTMonodromy (δ : ℂ) : Mat2C :=
  Complex.exp (2 * Real.pi * Complex.I * δ) • unipotentShear
    (2 * Real.pi * Complex.I)

def phase (δ : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * δ)

theorem logCFTMonodromy_eq_exp (δ : ℂ) :
    logCFTMonodromy δ =
      NormedSpace.exp ((2 * Real.pi * Complex.I) • jordanHamiltonian δ) := by
  rw [exp_smul_jordanHamiltonian]
  rfl

theorem phase_add (δ ε : ℂ) :
    phase (δ + ε) = phase δ * phase ε := by
  unfold phase
  rw [mul_add, Complex.exp_add]

theorem phase_mul_neg (δ : ℂ) :
    phase δ * phase (-δ) = 1 := by
  rw [← phase_add, add_neg_cancel, phase]
  simp

theorem logCFTMonodromy_factorization (δ : ℂ) :
    logCFTMonodromy δ =
      Complex.exp (2 * Real.pi * Complex.I * δ) •
        ((1 : Mat2C) + (2 * Real.pi * Complex.I) • nilpotentN) := by
  rfl

theorem unipotentShear_mul (τ σ : ℂ) :
    unipotentShear τ * unipotentShear σ = unipotentShear (τ + σ) := by
  unfold unipotentShear
  simp [add_mul, mul_add, nilpotentN_sq_zero, add_assoc, add_smul]

theorem unipotentShear_pow (τ : ℂ) (n : ℕ) :
    unipotentShear τ ^ n = 1 + n • (τ • nilpotentN) := by
  unfold unipotentShear
  apply InfoGeometry.Clifford.NilpotentBinomial.one_add_pow_of_sq_zero
  simp [nilpotentN_sq_zero]

theorem unipotentShear_mul_neg (τ : ℂ) :
    unipotentShear τ * unipotentShear (-τ) = 1 := by
  calc
    unipotentShear τ * unipotentShear (-τ) =
        unipotentShear (τ + -τ) := unipotentShear_mul τ (-τ)
    _ = 1 := by simp [unipotentShear]

theorem unipotentShear_neg_mul (τ : ℂ) :
    unipotentShear (-τ) * unipotentShear τ = 1 := by
  calc
    unipotentShear (-τ) * unipotentShear τ =
        unipotentShear (-τ + τ) := unipotentShear_mul (-τ) τ
    _ = 1 := by simp [unipotentShear]

theorem logCFTMonodromy_mul_inverse (δ : ℂ) :
    logCFTMonodromy δ *
        (phase (-δ) • unipotentShear (-(2 * Real.pi * Complex.I))) = 1 := by
  have hphase :
      Complex.exp (2 * Real.pi * Complex.I * δ) * phase (-δ) = 1 := by
    simpa [phase] using (phase_mul_neg δ)
  rw [logCFTMonodromy, smul_mul_smul, hphase,
    unipotentShear_mul_neg]
  simp

theorem logCFTMonodromy_inverse_mul (δ : ℂ) :
    (phase (-δ) • unipotentShear (-(2 * Real.pi * Complex.I))) *
        logCFTMonodromy δ = 1 := by
  have hphase :
      phase (-δ) * Complex.exp (2 * Real.pi * Complex.I * δ) = 1 := by
    simpa [phase, mul_comm] using (phase_mul_neg δ)
  rw [logCFTMonodromy, smul_mul_smul, hphase,
    unipotentShear_neg_mul]
  simp

theorem unipotentShear_pow_eq (τ : ℂ) (n : ℕ) :
    unipotentShear τ ^ n = unipotentShear ((n : ℂ) * τ) := by
  rw [unipotentShear_pow]
  unfold unipotentShear
  rw [← Nat.cast_smul_eq_nsmul ℂ n]
  simp [smul_smul, mul_comm]

end
end InfoGeometry.Physics.LogCFTJordanShear
