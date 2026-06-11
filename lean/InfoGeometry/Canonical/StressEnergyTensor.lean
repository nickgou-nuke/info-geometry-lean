import Mathlib.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Data.Complex.Basic

noncomputable section

namespace InfoGeometry.Canonical.EmergentGravity

open Complex

/-!
# Belinfante-Rosenfeld Stress-Energy Tensor

#### BUCKET 1: CLOSED FINITE THEOREMS
This file proves symmetry of a finite Belinfante-style tensor expression that is
defined by explicit symmetrization of abstract bilinear components.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The theorem is conditional on the abstract components `B` and `C` supplied in
`SpinorBilinearTensor`.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not derive the tensor from an action, prove conservation,
construct gamma matrices or covariant derivatives, or establish an
Einstein-Cartan source equation.
-/

/-- Abstract finite bilinear components used in the symmetrized tensor. -/
structure SpinorBilinearTensor (M : Type*) [AddCommGroup M] [Module ℂ M] where
  B : ℕ → ℕ → M
  C : ℕ → ℕ → M

/-- The Belinfante-Rosenfeld Stress-Energy Tensor:
    T_μν = (i/4) * [ bar{φ} γ_μ D_ν φ + bar{φ} γ_ν D_μ φ - (D_ν bar{φ}) γ_μ φ - (D_μ bar{φ}) γ_ν φ ]
         = (i/4) * [ B_μν + B_νμ - C_νμ - C_μν ] -/
def stress_energy_tensor {M : Type*} [AddCommGroup M] [Module ℂ M] 
    (tensor : SpinorBilinearTensor M) (mu nu : ℕ) : M :=
  (I / 4 : ℂ) • (tensor.B mu nu + tensor.B nu mu - tensor.C nu mu - tensor.C mu nu)

/-- The explicitly symmetrized finite stress-energy tensor is symmetric. -/
theorem stress_energy_symmetry {M : Type*} [AddCommGroup M] [Module ℂ M] 
    (tensor : SpinorBilinearTensor M) (mu nu : ℕ) :
    stress_energy_tensor tensor mu nu = stress_energy_tensor tensor nu mu := by
  dsimp [stress_energy_tensor]
  congr 1
  -- We must prove: B_μν + B_νμ - C_νμ - C_μν = B_νμ + B_μν - C_μν - C_νμ
  have h1 : tensor.B mu nu + tensor.B nu mu = tensor.B nu mu + tensor.B mu nu := add_comm _ _
  have h2 : tensor.C nu mu + tensor.C mu nu = tensor.C mu nu + tensor.C nu mu := add_comm _ _
  rw [sub_sub, sub_sub]
  rw [h1, h2]

end InfoGeometry.Canonical.EmergentGravity
