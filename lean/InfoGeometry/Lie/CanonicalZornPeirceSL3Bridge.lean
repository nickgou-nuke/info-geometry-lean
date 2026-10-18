/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornPeirceStabilizer
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Physics.SplitG2SL3Concrete

/-!
# The real `SL₃` readout of the canonical Peirce stabilizer

This module contains the coordinate-level part of the stabilizer bridge.  The
matrix readout is trace-zero by construction.  The remaining theorem that the
readout is a Lie equivalence with the full Peirce stabilizer is intentionally
separate from this finite coordinate calibration.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge

open InfoGeometry.Lie.CanonicalZornPeirceStabilizer
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev SL3 := InfoGeometry.Physics.SplitG2SL3Concrete.SL3

/-- The `3 × 3` matrix carried by the eight stabilizer parameters. -/
def parameterMatrix (p : Params) : Matrix3 :=
  ![![p 6 + p 13, -p 5, -p 11],
    ![-p 1, -p 6, -p 12],
    ![-p 2, -p 7, -p 13]]

@[simp] theorem parameterMatrix_trace_zero (p : Params) :
    Matrix.trace (parameterMatrix p) = 0 := by
  simp [parameterMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_three]

/-- The canonical real `SL₃` readout of a Peirce-stabilizing derivation. -/
def stabilizerMatrix (D : peirceStabilizer) : Matrix3 :=
  parameterMatrix
    (derivationParameters
      (canonicalToVectorDerivation D.1))

/-- The readout lands in the trace-zero carrier. -/
def stabilizerMatrixSL3 (D : peirceStabilizer) : SL3 :=
  ⟨stabilizerMatrix D, parameterMatrix_trace_zero _⟩

/-- Parameters selected from a trace-zero matrix.  The six parameters that
move the two diagonal Peirce idempotents are set to zero. -/
def sl3Parameters (M : SL3) : Params :=
  ![0,
    -M.1 1 0,
    -M.1 2 0,
    0,
    0,
    -M.1 0 1,
    -M.1 1 1,
    -M.1 2 1,
    0,
    0,
    0,
    -M.1 0 2,
    -M.1 1 2,
    -M.1 2 2]

/-- The selected parameters reconstruct the original trace-zero matrix. -/
theorem parameterMatrix_sl3Parameters (M : SL3) :
    parameterMatrix (sl3Parameters M) = M.1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parameterMatrix, sl3Parameters]
  · have htrace := M.2
    simp [Matrix.trace, Fin.sum_univ_three] at htrace
    linarith

/-- The canonical derivation represented by the selected parameters. -/
noncomputable def sl3StabilizerCandidate (M : SL3) : Deriv :=
  canonicalParameterLinearEquiv (sl3Parameters M)

@[simp] theorem sl3StabilizerCandidate_fixes_plus (M : SL3) :
    (sl3StabilizerCandidate M).1 peircePlus = 0 := by
  apply canonicalVectorEquiv.injective
  simp [sl3StabilizerCandidate, canonicalParameterLinearEquiv,
    vectorCanonicalLieEquiv, vectorCanonicalLinearEquiv,
    vectorToCanonicalDerivation, parameterLinearEquiv,
    parameterDerivation, parameterAction, sl3Parameters,
    peircePlus, E11, E22, U, V]
  rfl

@[simp] theorem sl3StabilizerCandidate_fixes_minus (M : SL3) :
    (sl3StabilizerCandidate M).1 peirceMinus = 0 := by
  apply canonicalVectorEquiv.injective
  simp [sl3StabilizerCandidate, canonicalParameterLinearEquiv,
    vectorCanonicalLieEquiv, vectorCanonicalLinearEquiv,
    vectorToCanonicalDerivation, parameterLinearEquiv,
    parameterDerivation, parameterAction, sl3Parameters,
    peirceMinus, E11, E22, U, V]
  rfl

/-- The selected parameter derivation belongs to the intrinsic Peirce
stabilizer. -/
noncomputable def sl3ToPeirceStabilizer (M : SL3) : peirceStabilizer :=
  ⟨sl3StabilizerCandidate M,
    sl3StabilizerCandidate_fixes_plus M,
    sl3StabilizerCandidate_fixes_minus M⟩

/-- The coordinate readout has an explicit right inverse at the `SL₃` matrix
level. -/
theorem stabilizerMatrixSL3_value (M : SL3) :
    parameterMatrix (sl3Parameters M) = M.1 :=
  parameterMatrix_sl3Parameters M

/-- The selected derivation reads back to its source matrix under the full
stabilizer map, not just under the raw parameter-matrix calculation. -/
theorem stabilizerMatrixSL3_sl3ToPeirceStabilizer (M : SL3) :
    stabilizerMatrixSL3 (sl3ToPeirceStabilizer M) = M := by
  apply Subtype.ext
  change parameterMatrix
    (derivationParameters
      (canonicalToVectorDerivation
        (canonicalParameterLinearEquiv (sl3Parameters M)))) = M.1
  have hparam :
      derivationParameters
        (canonicalToVectorDerivation
          (canonicalParameterLinearEquiv (sl3Parameters M))) =
        sl3Parameters M := by
    change parameterLinearEquiv.symm
      (parameterLinearEquiv (sl3Parameters M)) = _
    exact parameterLinearEquiv.left_inv _
  rw [hparam, parameterMatrix_sl3Parameters]

end InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge

end
