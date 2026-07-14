import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import InfoGeometry.Krein.DiracHodgeDoubledSpace

/-!
# Two-Sheet Complex Polarization

Finite real-matrix model of the two-sheet mechanism:

* sheet grading `epsilon = diag(1,-1)`;
* sheet swap `J`;
* emergent complex axis `K = J epsilon`;
* `K^2 = -1` follows from real involutions and anticommutation.

#### BUCKET 1: CLOSED FINITE THEOREMS
The finite real matrix identities for `J`, `epsilon`, `K`, sheet projectors,
and the Dirac-Hodge hopping operator.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The generic doubled-Krein theorem is imported from
`InfoGeometry.Krein.DiracHodgeDoubledSpace` for carriers satisfying its
explicit Hilbert-space typeclass premises.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove the Connes Standard Model, a Higgs vacuum expectation
value, a Bregman cooling-limit theorem, a Klein-bottle global-current
cancellation theorem, or an identification with `Cl^+(3,0; C)`.
-/

noncomputable section

open scoped Matrix

namespace TwoSheetComplexPolarization

/-- The finite real two-sheet carrier. -/
abbrev SheetMat : Type :=
  Matrix (Fin 2) (Fin 2) ℝ

/-- Sheet grading `epsilon = diag(1,-1)`. -/
def sheetGrading : SheetMat :=
  !![(1 : ℝ), 0; 0, -1]

/-- Sheet swap / Tomita-style modular conjugation `J`. -/
def sheetSwap : SheetMat :=
  !![(0 : ℝ), 1; 1, 0]

/-- Emergent real complex axis `K = J epsilon`. -/
def emergentComplexK : SheetMat :=
  sheetSwap * sheetGrading

/-- The left/physical sheet projector. -/
def physicalSheetProjector : SheetMat :=
  (1 / 2 : ℝ) • ((1 : SheetMat) + sheetGrading)

/-- The right/ghost sheet projector. -/
def ghostSheetProjector : SheetMat :=
  (1 / 2 : ℝ) • ((1 : SheetMat) - sheetGrading)

/-- Left Cuntz-style finite shift. -/
def sheetShiftL : SheetMat :=
  !![(0 : ℝ), 1; 0, 0]

/-- Right Cuntz-style finite shift. -/
def sheetShiftR : SheetMat :=
  !![(0 : ℝ), 0; 1, 0]

/-- Finite Dirac-Hodge hopping operator `D = S_L + J S_L J`. -/
def diracHodgeHopping : SheetMat :=
  sheetShiftL + sheetSwap * sheetShiftL * sheetSwap

/-- Bregman free-energy potential used by the prose layer. -/
def bregmanFreeEnergy (x : ℝ) : ℝ :=
  Real.exp x - 1 - x

@[simp] theorem sheetSwap_sq :
    sheetSwap * sheetSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sheetSwap, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem sheetGrading_sq :
    sheetGrading * sheetGrading = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sheetGrading, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two real involutions anticommute. -/
theorem sheetSwap_sheetGrading_anticommute :
    sheetSwap * sheetGrading = -(sheetGrading * sheetSwap) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sheetSwap, sheetGrading, Matrix.mul_apply, Fin.sum_univ_two]

/-- Explicit matrix for the emergent real complex axis. -/
theorem emergentComplexK_eq :
    emergentComplexK = !![(0 : ℝ), -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [emergentComplexK, sheetSwap, sheetGrading, Matrix.mul_apply, Fin.sum_univ_two]

/-- The emergent real complex axis squares to `-1`. -/
@[simp] theorem emergentComplexK_sq :
    emergentComplexK * emergentComplexK = -(1 : SheetMat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [emergentComplexK, sheetSwap, sheetGrading, Matrix.mul_apply, Fin.sum_univ_two]

/-- Sheet swap conjugates the emergent complex axis to its negative. -/
@[simp] theorem sheetSwap_conj_emergentComplexK :
    sheetSwap * emergentComplexK * sheetSwap = -emergentComplexK := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [emergentComplexK, sheetSwap, sheetGrading, Matrix.mul_apply, Fin.sum_univ_two]

/-- The physical sheet projector is explicitly diagonal. -/
@[simp] theorem physicalSheetProjector_eq :
    physicalSheetProjector = !![(1 : ℝ), 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [physicalSheetProjector, sheetGrading]

/-- The ghost sheet projector is explicitly diagonal. -/
@[simp] theorem ghostSheetProjector_eq :
    ghostSheetProjector = !![(0 : ℝ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ghostSheetProjector, sheetGrading]

@[simp] theorem physicalSheetProjector_idempotent :
    physicalSheetProjector * physicalSheetProjector = physicalSheetProjector := by
  rw [physicalSheetProjector_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem ghostSheetProjector_idempotent :
    ghostSheetProjector * ghostSheetProjector = ghostSheetProjector := by
  rw [ghostSheetProjector_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem physical_ghost_projectors_complement :
    physicalSheetProjector + ghostSheetProjector = 1 := by
  rw [physicalSheetProjector_eq, ghostSheetProjector_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- Conjugating the left shift by sheet swap gives the right shift. -/
@[simp] theorem sheetSwap_conj_shiftL :
    sheetSwap * sheetShiftL * sheetSwap = sheetShiftR := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sheetSwap, sheetShiftL, sheetShiftR, Matrix.mul_apply, Fin.sum_univ_two]

/-- The finite Dirac-Hodge hopping operator is the sum of the two sheet shifts. -/
theorem diracHodgeHopping_eq_shift_sum :
    diracHodgeHopping = sheetShiftL + sheetShiftR := by
  simp [diracHodgeHopping]

/-- Explicit matrix for the finite Dirac-Hodge hopping operator. -/
theorem diracHodgeHopping_eq_sheetSwap :
    diracHodgeHopping = sheetSwap := by
  rw [diracHodgeHopping_eq_shift_sum]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sheetSwap, sheetShiftL, sheetShiftR]

@[simp] theorem bregmanFreeEnergy_zero :
    bregmanFreeEnergy 0 = 0 := by
  simp [bregmanFreeEnergy]

/--
Finite package: the two-sheet real model produces a square-minus-one complex
axis from two real involutions and identifies the Dirac-Hodge hop with the sheet
swap.
-/
theorem twoSheetPolarizationPackage :
    sheetSwap * sheetSwap = 1
      ∧ sheetGrading * sheetGrading = 1
      ∧ sheetSwap * sheetGrading = -(sheetGrading * sheetSwap)
      ∧ emergentComplexK * emergentComplexK = -(1 : SheetMat)
      ∧ physicalSheetProjector + ghostSheetProjector = 1
      ∧ diracHodgeHopping = sheetSwap
      ∧ bregmanFreeEnergy 0 = 0 := by
  exact ⟨sheetSwap_sq, sheetGrading_sq, sheetSwap_sheetGrading_anticommute,
    emergentComplexK_sq, physical_ghost_projectors_complement,
    diracHodgeHopping_eq_sheetSwap, bregmanFreeEnergy_zero⟩

end TwoSheetComplexPolarization

