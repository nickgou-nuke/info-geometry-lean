/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.TwistorKinematicTensor

/-! Mixed-index moment operators from the upstream Perjes holonomy branch.
The actual matrix operator is distinct from the symmetric kinematic tensor.
The square identity and noncommuting null witnesses use the existing Witt form.
-/
noncomputable section
namespace InfoGeometry.Twistor.PerjesMomentOperator
open PenroseIncidence PerjesConventions TwistorKinematicTensor Matrix
open scoped BigOperators Matrix

def conjugateCoordinate (Z : Twistor4) : Slot → ℂ :=
  Sum.elim (star Z.2) (star Z.1)

/-- A mixed-index operator; unlike `kinematic`, it composes as an endomorphism. -/
def momentOperator (Z : Twistor4) : KinematicMatrix :=
  vecMulVec (component Z) (conjugateCoordinate Z)

theorem momentOperator_square (Z : Twistor4) :
    momentOperator Z * momentOperator Z = wittPair Z Z • momentOperator Z := by
  ext a b
  simp [momentOperator, vecMulVec, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, wittPair, component, conjugateCoordinate,
    smul_eq_mul]
  ring

theorem null_momentOperator_square (Z : Twistor4) (hZ : wittPair Z Z = 0) :
    momentOperator Z * momentOperator Z = 0 := by
  rw [momentOperator_square, hZ, zero_smul]

/-- Genuine noncommutativity, even on two null rank-one moment operators. -/
theorem momentOperators_noncommuting :
    ∃ Z W : Twistor4,
      wittPair Z Z = 0 ∧ wittPair W W = 0 ∧
      momentOperator Z * momentOperator W ≠ momentOperator W * momentOperator Z := by
  let Z : Twistor4 := (![1, 0], 0)
  let W : Twistor4 := (0, ![1, 0])
  refine ⟨Z, W, by simp [Z, wittPair], by simp [W, wittPair], ?_⟩
  intro h
  have h00 := congrArg (fun M : KinematicMatrix => M (.inl 0) (.inl 0)) h
  norm_num [momentOperator, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    vecMulVec, component, conjugateCoordinate, Z, W] at h00


end InfoGeometry.Twistor.PerjesMomentOperator
