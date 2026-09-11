/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction

namespace InfoGeometry.Exceptional.G2DiagonalPhase

noncomputable section

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction

/-!
# Diagonal phase data on the signed `G₂` root carrier

The table below is an explicit datum: a phase `ζ` is assigned to positive
roots and its inverse to negative roots.  This owner intentionally proves
only the diagonal readback.  Compatibility with a Weyl reflection is a
separate theorem and is not inferred from diagonality.
-/

abbrev Root := G2CoordinateRoot
abbrev RootOperator := Matrix Root Root ℂ

noncomputable def signedPhase (ζ : ℂ) (r : Root) : ℂ := by
  classical
  exact if isPositive r then ζ else ζ⁻¹

def phaseTable (ζ : ℂ) : Root → ℂ := signedPhase ζ

def phaseMatrix (ζ : ℂ) : RootOperator :=
  Matrix.diagonal (phaseTable ζ)

@[simp] theorem phaseMatrix_apply (ζ : ℂ) (i j : Root) :
    phaseMatrix ζ i j = if i = j then phaseTable ζ i else 0 := by
  classical
  simp [phaseMatrix, Matrix.diagonal_apply]

@[simp] theorem phaseMatrix_diag (ζ : ℂ) (i : Root) :
    phaseMatrix ζ i i = phaseTable ζ i := by
  classical
  simp [phaseMatrix]

theorem phaseTable_positive (ζ : ℂ) {r : Root} (hr : isPositive r) :
    phaseTable ζ r = ζ := by
  classical
  simp [phaseTable, signedPhase, hr]

theorem phaseTable_negative (ζ : ℂ) {r : Root} (hr : isNegative r) :
    phaseTable ζ r = ζ⁻¹ := by
  classical
  have hnot : ¬ isPositive r := by
    intro hpos
    exact (Finset.disjoint_left.mp phiPlus_disjoint_phiMinus) hpos hr
  simp [phaseTable, signedPhase, hnot]

structure DiagonalPhaseTable where
  ζ : ℂ

def DiagonalPhaseTable.table (d : DiagonalPhaseTable) : Root → ℂ :=
  phaseTable d.ζ

def DiagonalPhaseTable.matrix (d : DiagonalPhaseTable) : RootOperator :=
  Matrix.diagonal d.table

@[simp] theorem table_matrix_entry (d : DiagonalPhaseTable) (r : Root) :
    d.matrix r r = d.table r := by
  simp [DiagonalPhaseTable.matrix]

end
end InfoGeometry.Exceptional.G2DiagonalPhase
