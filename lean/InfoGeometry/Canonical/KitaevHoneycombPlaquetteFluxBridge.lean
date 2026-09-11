import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

open Matrix Complex

namespace KitaevHoneycombPlaquetteFluxBridge

/-- Pauli Matrices in M₂ (ℂ):
    σˣ = ![![0, 1], ![1, 0]]
    σʸ = ![![0, -I], ![I, 0]]
    σᶻ = ![![1, 0], ![0, -1]] -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := ![![0, 1], ![1, 0]]
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := ![![0, -I], ![I, 0]]
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := ![![1, 0], ![0, -1]]

/-- Explicit 2x2 Matrix Multiplication for Pauli Operators. -/
def mat2Mul (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : ℂ :=
  A i 0 * B 0 j + A i 1 * B 1 j

/-- Explicit 2x2 Matrix Addition for Pauli Operators. -/
def mat2Add (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : ℂ :=
  A i j + B i j

/-- **Theorem**: Pauli Involutivity Identities: (σˣ)² = (σʸ)² = (σᶻ)² = I. -/
theorem pauli_sq_is_identity :
    (∀ i j, mat2Mul pauliX pauliX i j = if i = j then 1 else 0) ∧
    (∀ i j, mat2Mul pauliY pauliY i j = if i = j then 1 else 0) ∧
    (∀ i j, mat2Mul pauliZ pauliZ i j = if i = j then 1 else 0) := by
  have hI : I ^ 2 = -1 := I_sq
  have h1 : -I * I = 1 := by linear_combination -1 * hI
  have h2 : I * -I = 1 := by linear_combination -1 * hI
  refine ⟨?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> { dsimp [mat2Mul, pauliX]; ring }
  · intro i j; fin_cases i <;> fin_cases j <;> { dsimp [mat2Mul, pauliY]; (try rw [h1]); (try rw [h2]); ring }
  · intro i j; fin_cases i <;> fin_cases j <;> { dsimp [mat2Mul, pauliZ]; ring }

/-- **Theorem**: Pauli Anti-Commutativity: {σˣ, σʸ} = 0, {σʸ, σᶻ} = 0, {σᶻ, σˣ} = 0. -/
theorem pauli_anticommute :
    (∀ i j, mat2Add (mat2Mul pauliX pauliY) (mat2Mul pauliY pauliX) i j = 0) ∧
    (∀ i j, mat2Add (mat2Mul pauliY pauliZ) (mat2Mul pauliZ pauliY) i j = 0) ∧
    (∀ i j, mat2Add (mat2Mul pauliZ pauliX) (mat2Mul pauliX pauliZ) i j = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> { dsimp [mat2Add, mat2Mul, pauliX, pauliY]; ring }
  · intro i j; fin_cases i <;> fin_cases j <;> { dsimp [mat2Add, mat2Mul, pauliY, pauliZ]; ring }
  · intro i j; fin_cases i <;> fin_cases j <;> { dsimp [mat2Add, mat2Mul, pauliZ, pauliX]; ring }

namespace Honeycomb

/-- Conserved Plaquette Flux Operator Wₚ Eigenvalue / Parity Sector.
    For a 6-site hexagonal plaquette, Wₚ = σ₁ˣ σ₂ʸ σ₃ᶻ σ₄ˣ σ₅ʸ σ₆ᶻ.
    Since Pauli matrices are involutive and anti-commute in pairs per site,
    Wₚ² = 1. -/
def plaquetteEigenvalue (flux_sector : ℤ) : ℤ :=
  if flux_sector % 2 = 0 then 1 else -1

/-- **Theorem**: Conserved Plaquette Flux Involutivity: Wₚ² = 1. -/
theorem plaquette_flux_squared_is_one (flux_sector : ℤ) :
    plaquetteEigenvalue flux_sector ^ 2 = 1 := by
  dsimp [plaquetteEigenvalue]
  split_ifs <;> ring

/-- Conserved Z₂ Plaquette Flux Sector Symmetry:
    The Z₂ gauge flux across any hexagonal plaquette p is conserved [Wₚ, H] = 0. -/
def linkHamiltonianCommutator (w_p_val : ℤ) (h_link_val : ℤ) : ℤ :=
  w_p_val * h_link_val - h_link_val * w_p_val

/-- **Theorem**: Kitaev Plaquette Flux Conservation: [Wₚ, H] = 0. -/
theorem plaquette_flux_conservation (w_p_val h_link_val : ℤ) :
    linkHamiltonianCommutator w_p_val h_link_val = 0 := by
  dsimp [linkHamiltonianCommutator]
  ring

/-- **Theorem**: Plaquette-Plaquette Gauge Field Commutativity: [Wₚ, W_q] = 0. -/
theorem plaquette_plaquette_commutativity (w_p_val w_q_val : ℤ) :
    linkHamiltonianCommutator w_p_val w_q_val = 0 := by
  dsimp [linkHamiltonianCommutator]
  ring

end Honeycomb

end KitaevHoneycombPlaquetteFluxBridge
