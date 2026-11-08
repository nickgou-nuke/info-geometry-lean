/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwistorInternalSymmetry

/-! # Column coordinates for the existing constituent packets

Contract: preserve the two upper and two lower spinor coordinates in that order.
The map is a complex-linear equivalence, and its matrix entries coincide with
the existing packetMatrix after transposition and the standard slot reindexing.
The infinity-raising matrix below expresses the existing antilinear operation.
-/
noncomputable section
namespace InfoGeometry.Twistor.ConstituentColumnEquivalence
open PenroseIncidence TwistorKinematicTensor TwistorConstituentKinematics
open scoped Matrix

variable {ι : Type*}

/-- Four-coordinate columns of the existing pairs of two-spinors. -/
def columnEquiv : Packet ι ≃ₗ[ℂ] Matrix (Fin 4) ι ℂ where
  toFun Z := fun a i => ![(Z i).1 0, (Z i).1 1, (Z i).2 0, (Z i).2 1] a
  invFun X := fun i => (![X 0 i, X 1 i], ![X 2 i, X 3 i])
  left_inv Z := by
    funext i
    apply Prod.ext <;> funext a <;> fin_cases a <;> rfl
  right_inv X := by
    funext a i
    fin_cases a <;> rfl
  map_add' Z W := by
    funext a i
    fin_cases a <;> rfl
  map_smul' c Z := by
    funext a i
    fin_cases a <;> rfl

/-- Exact agreement with the existing row-indexed packet matrix. -/
theorem columnEquiv_packetMatrix [Fintype ι] (Z : Packet ι) (a : Slot) (i : ι) :
    columnEquiv Z (finSumFinEquiv a) i = packetMatrix Z i a := by
  rcases a with a | a <;> fin_cases a <;> rfl

/-- Coordinate matrix of epsilon raising followed by the upper-spinor inclusion. -/
def infinityRaisingMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 1; 0, 0, -1, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- Entrywise conjugation and ordered multiplication transport the actual infinity map. -/
theorem columnEquiv_infinityConjugate (Z : Packet ι) :
    columnEquiv (fun i => infinityConjugate (Z i)) =
      infinityRaisingMatrix * (columnEquiv Z).map star := by
  funext a i
  fin_cases a <;>
    simp [columnEquiv, infinityConjugate, raiseSpinor, infinityRaisingMatrix,
      Matrix.mul_apply, Fin.sum_univ_four] <;> rfl

/-- The column-coordinate tensor agrees with the existing tensor in every slot. -/
theorem column_kinematic [Fintype ι] (Z : Packet ι) (a b : Slot) :
    (columnEquiv Z * (columnEquiv (fun i => infinityConjugate (Z i)))ᵀ +
      columnEquiv (fun i => infinityConjugate (Z i)) * (columnEquiv Z)ᵀ)
        (finSumFinEquiv a) (finSumFinEquiv b) = totalKinematic Z a b := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    columnEquiv_packetMatrix]
  rw [← Finset.sum_add_distrib]
  simp [totalKinematic, kinematic, symmetricOuter, packetMatrix, Matrix.sum_apply]

/-- Constituent mixing becomes right multiplication by the transposed label matrix. -/
theorem column_mix [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (Z : Packet ι) (a : Slot) (i : ι) :
    columnEquiv (TwistorInternalSymmetry.mix U Z) (finSumFinEquiv a) i =
      (columnEquiv Z * Uᵀ) (finSumFinEquiv a) i := by
  rw [columnEquiv_packetMatrix, TwistorInternalSymmetry.packetMatrix_mix]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, columnEquiv_packetMatrix]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The skew shift uses the same transpose convention as the mixing map. -/
theorem column_shift [Fintype ι] [DecidableEq ι]
    (L : Matrix ι ι ℂ) (Z : Packet ι) (a : Slot) (i : ι) :
    columnEquiv (TwistorInternalSymmetry.shift L Z) (finSumFinEquiv a) i =
      (columnEquiv Z + columnEquiv (fun j => infinityConjugate (Z j)) * Lᵀ)
        (finSumFinEquiv a) i := by
  rw [columnEquiv_packetMatrix, TwistorInternalSymmetry.packetMatrix_shift]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    columnEquiv_packetMatrix]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end InfoGeometry.Twistor.ConstituentColumnEquivalence
