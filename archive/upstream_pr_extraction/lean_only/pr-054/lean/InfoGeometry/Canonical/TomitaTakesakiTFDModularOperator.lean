import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Complex Real Finset

/-- A finite-dimensional quantum system with an energy spectrum E_i 
    and inverse temperature β = 1 / (k_B T). -/
structure QuantumSystem (n : Type*) [Fintype n] [DecidableEq n] where
  E : n → ℝ       -- Energy spectrum
  β : ℝ           -- Inverse temperature β
  β_pos : 0 < β   -- Thermal state requirement

namespace QuantumSystem

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (sys : QuantumSystem n)

/-- The Partition Function Z(β) = ∑_i exp(-β E_i) -/
def Z : ℝ := ∑ i : n, Real.exp (-sys.β * sys.E i)

/-- Partition function positivity guarantee -/
lemma Z_pos : 0 < sys.Z := by
  dsimp [Z]
  apply Finset.sum_pos
  · intro i _
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- The Thermofield Double (TFD) state vector in H_L ⊗ H_R ≅ ℓ²(n × n, ℂ). -/
def tfdState : (n × n) → ℂ :=
  fun ⟨i, j⟩ =>
    if i = j then
      (1 / Real.sqrt sys.Z : ℂ) * Complex.exp (-sys.β * sys.E i / 2)
    else
      0

/-- The Tomita-Takesaki Modular Operator Δ acting on the doubled Hilbert space H_L ⊗ H_R. -/
def modularOp (ψ : (n × n) → ℂ) : (n × n) → ℂ :=
  fun ⟨i, j⟩ => Complex.exp (-sys.β * (sys.E i - sys.E j)) * ψ ⟨i, j⟩

/-- The Modular Hamiltonian K = -ln Δ = β (H_L ⊗ I - I ⊗ H_R). -/
def modularHamiltonian (ψ : (n × n) → ℂ) : (n × n) → ℂ :=
  fun ⟨i, j⟩ => (sys.β * (sys.E i - sys.E j) : ℂ) * ψ ⟨i, j⟩

/-- Tomita-Takesaki Modular Time Flow σ_s = Δ^(is) = exp(-i s K). -/
def modularFlow (s : ℝ) (ψ : (n × n) → ℂ) : (n × n) → ℂ :=
  fun ⟨i, j⟩ => Complex.exp (-I * s * sys.β * (sys.E i - sys.E j)) * ψ ⟨i, j⟩

/-- **Theorem**: Action of the Modular Operator Δ on energy basis states |i, j⟩. -/
theorem modularOp_basis (i j : n) :
    sys.modularOp (fun ⟨a, b⟩ => if a = i ∧ b = j then 1 else 0) =
    fun ⟨a, b⟩ => if a = i ∧ b = j then Complex.exp (-sys.β * (sys.E i - sys.E j)) else 0 := by
  ext ⟨a, b⟩
  dsimp [modularOp]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    ring
  · ring

/-- **Theorem**: The TFD state is invariant under the Modular Operator: Δ |TFD⟩ = |TFD⟩. -/
theorem tfd_modularOp_invariant : sys.modularOp sys.tfdState = sys.tfdState := by
  ext ⟨i, j⟩
  dsimp [modularOp, tfdState]
  split_ifs with h
  · subst h
    have h_diff : (sys.E i : ℂ) - (sys.E i : ℂ) = 0 := sub_self _
    rw [h_diff, mul_zero, Complex.exp_zero, one_mul]
  · ring

/-- **Theorem**: The TFD state is invariant under Modular Time Flow: σ_s |TFD⟩ = |TFD⟩. -/
theorem tfd_modularFlow_invariant (s : ℝ) : sys.modularFlow s sys.tfdState = sys.tfdState := by
  ext ⟨i, j⟩
  dsimp [modularFlow, tfdState]
  split_ifs with h
  · subst h
    have h_diff : (sys.E i : ℂ) - (sys.E i : ℂ) = 0 := sub_self _
    rw [h_diff, mul_zero, Complex.exp_zero, one_mul]
  · ring

/-- Thermal expectation value in the KMS state ⟨A⟩_β = Tr(ρ_β A). -/
def thermalExpectation (A : n → n → ℂ) : ℂ :=
  (1 / (sys.Z : ℂ)) * ∑ i : n, Complex.exp (-sys.β * sys.E i) * A i i

/-- Heisenberg time evolution of an operator A under physical Hamiltonian H: A(t) = e^(iHt) A e^(-iHt). -/
def timeEvolve (A : n → n → ℂ) (t : ℂ) : n → n → ℂ :=
  fun i j => A i j * Complex.exp (I * t * (sys.E i - sys.E j))

/-- **Theorem**: The Kubo-Martin-Schwinger (KMS) Condition.
    Thermal correlation functions satisfy periodicity in imaginary time: 
    ⟨A(t) B(0)⟩_β = ⟨B(0) A(t + iβ)⟩_β. -/
theorem kms_condition (A B : n → n → ℂ) (t : ℝ) :
    sys.thermalExpectation (fun i j => ∑ k, sys.timeEvolve A t i k * B k j) =
    sys.thermalExpectation (fun i j => ∑ k, B i k * sys.timeEvolve A (t + I * sys.β) k j) := by
  dsimp [thermalExpectation, timeEvolve]
  congr 1
  -- Step 1: Expand LHS to sum over (i, k)
  have hL : (∑ i : n, Complex.exp (-sys.β * sys.E i) * ∑ k : n, A i k * Complex.exp (I * t * (sys.E i - sys.E k)) * B k i) =
            ∑ i : n, ∑ k : n, Complex.exp (-sys.β * sys.E i) * (A i k * Complex.exp (I * t * (sys.E i - sys.E k)) * B k i) := by
    apply sum_congr rfl; intro i _; exact Finset.mul_sum (univ : Finset n) (fun k => A i k * Complex.exp (I * ↑t * (↑(sys.E i) - ↑(sys.E k))) * B k i) (Complex.exp (-↑sys.β * ↑(sys.E i)))
  -- Step 2: Expand RHS to sum over (i, k)
  have hR : (∑ i : n, Complex.exp (-sys.β * sys.E i) * ∑ k : n, B i k * (A k i * Complex.exp (I * (t + I * sys.β) * (sys.E k - sys.E i)))) =
            ∑ i : n, ∑ k : n, Complex.exp (-sys.β * sys.E i) * (B i k * (A k i * Complex.exp (I * (t + I * sys.β) * (sys.E k - sys.E i)))) := by
    apply sum_congr rfl; intro i _; exact Finset.mul_sum (univ : Finset n) (fun k => B i k * (A k i * Complex.exp (I * (↑t + I * ↑sys.β) * (↑(sys.E k) - ↑(sys.E i))))) (Complex.exp (-↑sys.β * ↑(sys.E i)))
  rw [hL, hR, Finset.sum_comm]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro k _
  have h1 : Complex.exp (-sys.β * sys.E k) * Complex.exp (I * t * (sys.E k - sys.E i)) =
            Complex.exp (-sys.β * sys.E i) * Complex.exp (I * (t + I * sys.β) * (sys.E k - sys.E i)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have hI2 : I ^ 2 = -1 := I_sq
    calc -sys.β * sys.E k + I * t * (sys.E k - sys.E i)
      _ = -sys.β * sys.E k + I * t * (sys.E k - sys.E i) + (I ^ 2 + 1) * (sys.β * (sys.E k - sys.E i)) := by rw [hI2]; ring
      _ = -sys.β * sys.E i + I * (t + I * sys.β) * (sys.E k - sys.E i) := by ring
  calc Complex.exp (-sys.β * sys.E k) * (A k i * Complex.exp (I * t * (sys.E k - sys.E i)) * B i k)
    _ = (Complex.exp (-sys.β * sys.E k) * Complex.exp (I * t * (sys.E k - sys.E i))) * A k i * B i k := by ring
    _ = (Complex.exp (-sys.β * sys.E i) * Complex.exp (I * (t + I * sys.β) * (sys.E k - sys.E i))) * A k i * B i k := by rw [h1]
    _ = Complex.exp (-sys.β * sys.E i) * (B i k * (A k i * Complex.exp (I * (t + I * sys.β) * (sys.E k - sys.E i)))) := by ring

end QuantumSystem
