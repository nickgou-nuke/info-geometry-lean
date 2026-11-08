/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Twistor.TwistorConstituentKinematics

/-!
# Internal transformations of actual constituent twistors

Equation (6.14) has two different operations: unitary mixing and a skew
complex shift along the square-zero antilinear infinity map. We construct
both actions, their inverses and their invariance on the same kinematic
matrix. This is not a classification of the full stabilizer.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwistorInternalSymmetry

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.TwistorKinematicTensor
open InfoGeometry.Twistor.TwistorConstituentKinematics
open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise conjugation, deliberately distinct from the matrix star/adjoint. -/
def conjugateEntries (U : Matrix ι ι ℂ) : Matrix ι ι ℂ := fun i j => star (U i j)

/-- Linear mixing of the constituent labels. -/
def mix (U : Matrix ι ι ℂ) (Z : Packet ι) : Packet ι :=
  fun i => ∑ j, U i j • Z j

/-- The skew-shift term in the paper's internal transformation. -/
def shift (L : Matrix ι ι ℂ) (Z : Packet ι) : Packet ι :=
  fun i => Z i + ∑ j, L i j • infinityConjugate (Z j)

theorem packetMatrix_mix (U : Matrix ι ι ℂ) (Z : Packet ι) :
    packetMatrix (mix U Z) = U * packetMatrix Z := by
  ext i a
  simp [packetMatrix, mix, Matrix.mul_apply]

theorem infinityMatrix_mix (U : Matrix ι ι ℂ) (Z : Packet ι) :
    infinityMatrix (mix U Z) = conjugateEntries U * infinityMatrix Z := by
  ext i a
  simp [infinityMatrix, packetMatrix, mix, Matrix.mul_apply, conjugateEntries]

theorem packetMatrix_shift (L : Matrix ι ι ℂ) (Z : Packet ι) :
    packetMatrix (shift L Z) = packetMatrix Z + L * infinityMatrix Z := by
  ext i a
  simp [packetMatrix, shift, infinityMatrix, Matrix.mul_apply]

@[simp] theorem infinityConjugate_shift (L : Matrix ι ι ℂ) (Z : Packet ι) (i : ι) :
    infinityConjugate (shift L Z i) = infinityConjugate (Z i) := by
  simp [shift]

@[simp] theorem infinityMatrix_shift (L : Matrix ι ι ℂ) (Z : Packet ι) :
    infinityMatrix (shift L Z) = infinityMatrix Z := by
  ext i a
  simp [infinityMatrix, packetMatrix]

/-- The nilpotent shifts are additive, not a second independent oscillator. -/
theorem shift_add (L M : Matrix ι ι ℂ) (Z : Packet ι) :
    shift L (shift M Z) = shift (L + M) Z := by
  funext i
  simp [shift, add_smul, Finset.sum_add_distrib]
  abel

@[simp] theorem shift_zero (Z : Packet ι) : shift (0 : Matrix ι ι ℂ) Z = Z := by
  funext i
  simp [shift]

/-- Each skew shift is an actual bijection; skewness is needed for invariance,
not for the inverse construction. -/
def shiftEquiv (L : Matrix ι ι ℂ) : Equiv.Perm (Packet ι) where
  toFun := shift L
  invFun := shift (-L)
  left_inv Z := by rw [shift_add]; simp
  right_inv Z := by rw [shift_add]; simp

lemma mix_one (Z : Packet ι) : mix (1 : Matrix ι ι ℂ) Z = Z := by
  funext i
  simp [mix, Matrix.one_apply]

lemma mix_mul (U V : Matrix ι ι ℂ) (Z : Packet ι) :
    mix U (mix V Z) = mix (U * V) Z := by
  apply packetMatrix_injective
  rw [packetMatrix_mix, packetMatrix_mix, packetMatrix_mix, Matrix.mul_assoc]

/-- Unitary mixing as an actual equivalence; both inverse equations are explicit. -/
def mixEquiv (U : Matrix ι ι ℂ) (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1) :
    Equiv.Perm (Packet ι) where
  toFun := mix U
  invFun := mix Uᴴ
  left_inv Z := by rw [mix_mul, hleft, mix_one]
  right_inv Z := by rw [mix_mul, hright, mix_one]

private lemma transpose_unitary (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) :
    Uᵀ * conjugateEntries U = 1 := by
  have h := congrArg Matrix.transpose hU
  rw [Matrix.transpose_mul, Matrix.conjTranspose_transpose] at h
  have hc : U.map star = conjugateEntries U := by
    ext i j
    rfl
  rw [← hc]
  simpa using h

/-- Unitary changes of constituent frame preserve the full kinematic tensor. -/
theorem totalKinematic_mix (U : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) (Z : Packet ι) :
    totalKinematic (mix U Z) = totalKinematic Z := by
  rw [totalKinematic_matrix, packetMatrix_mix, infinityMatrix_mix,
    Matrix.transpose_mul, Matrix.transpose_mul, totalKinematic_matrix]
  have hV : (conjugateEntries U)ᵀ * U = 1 := hU
  calc
    _ = (packetMatrix Z)ᵀ * ((Uᵀ * conjugateEntries U) * infinityMatrix Z) +
        (infinityMatrix Z)ᵀ * (((conjugateEntries U)ᵀ * U) * packetMatrix Z) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [transpose_unitary U hU, hV]; simp

/-- Skewness cancels the actual quadratic shift defect. -/
theorem shift_kinematic_defect (L : Matrix ι ι ℂ) (Z : Packet ι) :
    totalKinematic (shift L Z) - totalKinematic Z =
      (infinityMatrix Z)ᵀ * (Lᵀ + L) * infinityMatrix Z := by
  simp only [totalKinematic_matrix, packetMatrix_shift, infinityMatrix_shift,
    Matrix.transpose_add, Matrix.transpose_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc]
  abel

/-- Skewness cancels the actual quadratic shift defect. -/
theorem totalKinematic_shift (L : Matrix ι ι ℂ) (hL : Lᵀ = -L) (Z : Packet ι) :
    totalKinematic (shift L Z) = totalKinematic Z := by
  rw [totalKinematic_matrix, packetMatrix_shift, infinityMatrix_shift,
    Matrix.transpose_add, Matrix.transpose_mul, hL,
    Matrix.add_mul, Matrix.mul_add, totalKinematic_matrix]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- The literal two-stage transformation from (6.14). -/
def internalTransform (U L : Matrix ι ι ℂ) (Z : Packet ι) : Packet ι :=
  mix U (shift L Z)

theorem internalTransform_kinematic (U L : Matrix ι ι ℂ)
    (hU : Uᴴ * U = 1) (hL : Lᵀ = -L) (Z : Packet ι) :
    totalKinematic (internalTransform U L Z) = totalKinematic Z := by
  rw [internalTransform, totalKinematic_mix U hU, totalKinematic_shift L hL]

/-- The exact stabilizer inside permutations of the constituent carrier.
The named transformations are proved to belong; equality with a classified
internal group is not supplied as an assumption. -/
def kinematicStabilizer : Subgroup (Equiv.Perm (Packet ι)) where
  carrier := {e | ∀ Z, totalKinematic (e Z) = totalKinematic Z}
  one_mem' Z := rfl
  mul_mem' {e f} he hf Z := (he (f Z)).trans (hf Z)
  inv_mem' {e} he Z := by
    have h := he (e⁻¹ Z)
    simpa using h.symm

theorem shift_mem_stabilizer (L : Matrix ι ι ℂ) (hL : Lᵀ = -L) :
    shiftEquiv L ∈ kinematicStabilizer :=
  totalKinematic_shift L hL

theorem mix_mem_stabilizer (U : Matrix ι ι ℂ)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1) :
    mixEquiv U hleft hright ∈ kinematicStabilizer :=
  totalKinematic_mix U hleft

/-- A nonzero skew shift genuinely changes the constituents while preserving K. -/
theorem nontrivial_shift_witness :
    let Z : Packet (Fin 2) := ![((0 : Spinor2), ![1, 0]), ((0 : Spinor2), ![0, 1])]
    let L : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
    shift L Z ≠ Z ∧ totalKinematic (shift L Z) = totalKinematic Z := by
  intro Z L
  constructor
  · intro h
    have h0 := congrArg (fun W : Packet (Fin 2) => (W 0).1 0) h
    norm_num [Z, L, shift, infinityConjugate, raiseSpinor, Fin.sum_univ_two] at h0
  · apply totalKinematic_shift
    ext i j
    fin_cases i <;> fin_cases j <;> simp [L]

end InfoGeometry.Twistor.TwistorInternalSymmetry
