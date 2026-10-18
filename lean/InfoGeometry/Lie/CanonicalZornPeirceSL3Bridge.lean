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

@[simp] theorem sl3Parameters_add (M N : SL3) :
    sl3Parameters (M + N) = sl3Parameters M + sl3Parameters N := by
  funext i
  fin_cases i <;> simp [sl3Parameters] <;> ring

@[simp] theorem sl3Parameters_smul (r : ℝ) (M : SL3) :
    sl3Parameters (r • M) = r • sl3Parameters M := by
  funext i
  fin_cases i <;> simp [sl3Parameters]

/-- The selected Peirce-stabilizing derivation depends additively on its
trace-zero matrix parameter. -/
theorem sl3ToPeirceStabilizer_add (M N : SL3) :
    sl3ToPeirceStabilizer (M + N) =
      sl3ToPeirceStabilizer M + sl3ToPeirceStabilizer N := by
  apply Subtype.ext
  change canonicalParameterLinearEquiv (sl3Parameters (M + N)) = _
  rw [sl3Parameters_add]
  exact map_add canonicalParameterLinearEquiv _ _

/-- The selected Peirce-stabilizing derivation respects real scalar action. -/
theorem sl3ToPeirceStabilizer_smul (r : ℝ) (M : SL3) :
    sl3ToPeirceStabilizer (r • M) =
      r • sl3ToPeirceStabilizer M := by
  apply Subtype.ext
  change canonicalParameterLinearEquiv (sl3Parameters (r • M)) = _
  rw [sl3Parameters_smul]
  exact map_smul canonicalParameterLinearEquiv r _

/-- The selected trace-zero parameters act on the vector-Zorn carrier by the
standard representation on the upper slot and the contragredient representation
on the lower slot. -/
theorem sl3Parameters_parameterAction (M : SL3)
    (X : InfoGeometry.Algebra.ZornVectorMatrix ℝ) :
    parameterAction (sl3Parameters M) X =
      ⟨0, M.1.mulVec X.v, (-Matrix.transpose M.1).mulVec X.w, 0⟩ := by
  have hdiag : M.1 0 0 = -M.1 1 1 - M.1 2 2 := by
    have ht := M.2
    simp [Matrix.trace, Fin.sum_univ_three] at ht
    linarith
  apply InfoGeometry.Algebra.ZornVectorMatrix.ext
  · simp [parameterAction, sl3Parameters]
  · funext i
    fin_cases i
    all_goals simp_all [parameterAction, sl3Parameters,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    all_goals ring_nf
    all_goals simp
  · funext i
    fin_cases i
    all_goals simp_all [parameterAction, sl3Parameters,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]
    all_goals ring_nf
  · simp [parameterAction, sl3Parameters]

/-- On the native Peirce off-diagonal carrier, the selected derivation has the
same standard/contragredient action in the native coordinate chart. -/
theorem sl3ToPeirceStabilizer_restrictOffDiagonal_apply
    (M : SL3) (X : offDiagonal) :
    offDiagonalLinearEquiv
        (restrictOffDiagonal (sl3ToPeirceStabilizer M) X) =
      (M.1.mulVec (offDiagonalLinearEquiv X).1,
        (-Matrix.transpose M.1).mulVec (offDiagonalLinearEquiv X).2) := by
  have hAction :
      canonicalToVectorDerivation (sl3StabilizerCandidate M)
          (canonicalVectorEquiv X.1) =
        ⟨0, M.1.mulVec X.1.x, (-Matrix.transpose M.1).mulVec X.1.y, 0⟩ := by
    change parameterAction (sl3Parameters M) (canonicalVectorEquiv X.1) = _
    exact sl3Parameters_parameterAction M (canonicalVectorEquiv X.1)
  have hNative := canonicalToVectorDerivation_apply
      (sl3StabilizerCandidate M) (canonicalVectorEquiv X.1)
  rw [hAction] at hNative
  change ((restrictOffDiagonal (sl3ToPeirceStabilizer M) X).1.x,
      (restrictOffDiagonal (sl3ToPeirceStabilizer M) X).1.y) = _
  change (((sl3ToPeirceStabilizer M).1.1 X.1).x,
      ((sl3ToPeirceStabilizer M).1.1 X.1).y) = _
  have hx := congrArg
    (fun Z : InfoGeometry.Algebra.ZornVectorMatrix ℝ => Z.v) hNative
  have hy := congrArg
    (fun Z : InfoGeometry.Algebra.ZornVectorMatrix ℝ => Z.w) hNative
  have hx' :
      ((sl3StabilizerCandidate M).1 X.1).x = M.1.mulVec X.1.x := by
    simpa [canonicalVectorEquiv] using hx.symm
  have hy' :
      ((sl3StabilizerCandidate M).1 X.1).y =
        (-(Matrix.transpose M.1)).mulVec X.1.y := by
    simpa [canonicalVectorEquiv] using hy.symm
  exact Prod.ext hx' hy'

/-- The selected Peirce-stabilizer section is injective, since its matrix
readout is a left inverse. -/
theorem sl3ToPeirceStabilizer_injective :
    Function.Injective sl3ToPeirceStabilizer := by
  intro M N h
  have hread := congrArg stabilizerMatrixSL3 h
  rw [stabilizerMatrixSL3_sl3ToPeirceStabilizer,
    stabilizerMatrixSL3_sl3ToPeirceStabilizer] at hread
  exact hread

end InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge

end
