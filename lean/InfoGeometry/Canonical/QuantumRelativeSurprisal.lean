import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic

set_option linter.unusedSectionVars false

open Complex Matrix

namespace QuantumRelativeSurprisal

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 1. Relative Surprisal Operator K_(ρ|σ) = H_ρ - H_sigma
    where H_ρ = log ρ and H_σ = log σ are the modular Hamiltonians. -/
def relativeSurprisal (H_rho H_sigma : Matrix n n ℂ) : Matrix n n ℂ :=
  H_rho - H_sigma

/-- 2. Von Neumann Entropy S(ρ) = -Tr(ρ * H_ρ) -/
noncomputable def vonNeumannEntropy (rho H_rho : Matrix n n ℂ) : ℂ :=
  - trace (rho * H_rho)

/-- 3. Quantum Free Energy F(ρ) = Tr(ρ * H) - (1/β) * S(ρ) -/
noncomputable def freeEnergy (beta : ℂ) (H rho H_rho : Matrix n n ℂ) : ℂ :=
  trace (rho * H) + (1 / beta) * trace (rho * H_rho)

/-- 4. Thermal Equilibrium Modular Hamiltonian: H_σ = -β * H - c * I (where c = log Z) -/
def thermalModularHamiltonian (beta c : ℂ) (H : Matrix n n ℂ) : Matrix n n ℂ :=
  - beta • H - c • (1 : Matrix n n ℂ)

/-- 🏆 THEOREM 1: Expectation Value of Relative Surprisal equals Relative Entropy
    Tr(ρ * K_(ρ|σ)) = Tr(ρ * H_ρ) - Tr(ρ * H_σ) -/
theorem relativeSurprisal_expectation (rho H_rho H_sigma : Matrix n n ℂ) :
    trace (rho * relativeSurprisal H_rho H_sigma) = trace (rho * H_rho) - trace (rho * H_sigma) := by
  dsimp [relativeSurprisal]
  rw [mul_sub, trace_sub]

/-- 🏆 THEOREM 2: Connection between Relative Surprisal Expectation and Free Energy Difference
    For a normalized density matrix (Tr(ρ) = 1) and thermal state σ with log Z = c,
    Tr(ρ * K_(ρ|σ)) = β * (F(ρ) - F(σ)) where F(σ) = -c / β. -/
theorem relativeSurprisal_eq_beta_freeEnergy_diff
    (beta c : ℂ) (hbeta : beta ≠ 0)
    (H rho H_rho : Matrix n n ℂ)
    (h_norm : trace rho = 1) :
    trace (rho * relativeSurprisal H_rho (thermalModularHamiltonian beta c H)) =
    beta * (freeEnergy beta H rho H_rho - (- c / beta)) := by
  dsimp [relativeSurprisal, thermalModularHamiltonian, freeEnergy]
  rw [mul_sub, trace_sub]
  have h_tr_sigma : trace (rho * (-beta • H - c • 1)) = -beta * trace (rho * H) - c := by
    rw [mul_sub, trace_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one, trace_smul, trace_smul, h_norm]
    simp only [smul_eq_mul]
    ring
  rw [h_tr_sigma]
  field_simp [hbeta]
  ring

/-- 🏆 THEOREM 3: Directional Free Energy Derivative along Trace-Preserving Perturbations
    For any trace-zero perturbation δρ (Tr(δρ) = 0), the directional derivative
    Tr(δρ * K_(ρ|σ)) equals β * Tr(δρ * H) + Tr(δρ * H_ρ). -/
theorem relativeSurprisal_tangent_gradient
    (beta c : ℂ)
    (H H_rho delta_rho : Matrix n n ℂ)
    (h_tangent : trace delta_rho = 0) :
    trace (delta_rho * relativeSurprisal H_rho (thermalModularHamiltonian beta c H)) =
    beta * trace (delta_rho * H) + trace (delta_rho * H_rho) := by
  dsimp [relativeSurprisal, thermalModularHamiltonian]
  rw [mul_sub, trace_sub]
  have h_tr_sigma : trace (delta_rho * (-beta • H - c • 1)) = -beta * trace (delta_rho * H) := by
    rw [mul_sub, trace_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one, trace_smul, trace_smul, h_tangent]
    simp only [smul_eq_mul]
    ring
  rw [h_tr_sigma]
  ring

end QuantumRelativeSurprisal
