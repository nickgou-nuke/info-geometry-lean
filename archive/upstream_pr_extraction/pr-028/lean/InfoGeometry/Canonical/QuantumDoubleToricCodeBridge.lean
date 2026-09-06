import Mathlib.Analysis.Complex.Basic
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

namespace QuantumDoubleToricCodeBridge

/-- Simple Anyons in the Toric Code D(ℤ₂):
- `vacuum` (1): Trivial flux & trivial charge
- `e`      : Pure electric charge (star defect)
- `m`      : Pure magnetic flux (plaquette defect)
- `epsilon`: Dyon (e ⊗ m) -/
inductive ToricAnyon : Type
  | vacuum  : ToricAnyon
  | e       : ToricAnyon
  | m       : ToricAnyon
  | epsilon : ToricAnyon
  deriving DecidableEq

instance : Fintype ToricAnyon where
  elems := {ToricAnyon.vacuum, ToricAnyon.e, ToricAnyon.m, ToricAnyon.epsilon}
  complete := by rintro (_ | _ | _ | _) <;> decide

open ToricAnyon

/-- Gauge Group Order |G| = |ℤ₂| = 2. -/
def groupOrder : ℝ := 2

/-- Quantum dimensions: d_a = 1 for all abelian anyons in D(ℤ₂). -/
def quantumDim (a : ToricAnyon) : ℝ := 1

/-- **Theorem**: Total Quantum Dimension 𝒯 = √(1² + 1² + 1² + 1²) = √4 = 2 = |G|. -/
theorem total_quantum_dim :
    Real.sqrt (quantumDim vacuum ^ 2 + quantumDim e ^ 2 + quantumDim m ^ 2 + quantumDim epsilon ^ 2) = groupOrder := by
  dsimp [quantumDim, groupOrder]
  have h4 : (1 : ℝ) ^ 2 + 1 ^ 2 + 1 ^ 2 + 1 ^ 2 = (2 : ℝ) ^ 2 := by norm_num
  rw [h4]
  exact Real.sqrt_sq (by norm_num)

/-- The D(ℤ₂) Modular S-Matrix in M₄ (ℝ). -/
noncomputable def modularSMatrix : Matrix ToricAnyon ToricAnyon ℝ
  | vacuum,  _       => 1 / groupOrder
  | _,       vacuum  => 1 / groupOrder
  | e,       e       => 1 / groupOrder
  | e,       m       => -1 / groupOrder
  | e,       epsilon => -1 / groupOrder
  | m,       e       => -1 / groupOrder
  | m,       m       => 1 / groupOrder
  | m,       epsilon => -1 / groupOrder
  | epsilon, e       => -1 / groupOrder
  | epsilon, m       => -1 / groupOrder
  | epsilon, epsilon => 1 / groupOrder

/-- **Theorem**: Toric Code Modular S-Matrix Symmetry: Sᵀ = S. -/
theorem modularSMatrix_is_symmetric :
    modularSMatrix.transpose = modularSMatrix := by
  ext i j
  cases i <;> cases j <;> rfl

/-- **Theorem**: Aharonov-Bohm Mutual Braiding Phase: S_{e, m} = -1 / 2. -/
theorem aharonov_bohm_braiding_phase :
    modularSMatrix e m = -1 / 2 := by
  dsimp [modularSMatrix, groupOrder]

/-- Sum over all Toric Code anyons. -/
def toricSum (f : ToricAnyon → ℝ) : ℝ :=
  f vacuum + f e + f m + f epsilon

/-- **Theorem**: Toric Code S-Matrix Unitarity & Involution (S² = I) via Toric Sum. -/
theorem modularSMatrix_involution (i j : ToricAnyon) :
    toricSum (fun k => modularSMatrix i k * modularSMatrix k j) = if i = j then 1 else 0 := by
  dsimp [toricSum, modularSMatrix, groupOrder]
  cases i <;> cases j <;> norm_num <;> decide

end QuantumDoubleToricCodeBridge
