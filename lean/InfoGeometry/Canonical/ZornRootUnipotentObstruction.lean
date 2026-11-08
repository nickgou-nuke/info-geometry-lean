/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ZornChannelDerivations
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.NoncommRing

/-!
# A quadratic obstruction to exponentiating a Zorn derivation

The owner product is nonassociative. Consequently `id + D` for a derivation
does not automatically preserve multiplication: its multiplicativity defect
is the product `D X * D Y`.
-/

namespace InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion

variable {A : Type*} [Ring A]

def rootXYUpdate (X : OpZornMatrix A) : OpZornMatrix A := X + rootXY X

def rootZX (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨0, ⟨0, 0, X.v.x⟩, ⟨-X.w.z, 0, 0⟩, 0⟩

/-- For a derivation, the multiplicativity defect of `id + D` is exactly its
quadratic term. -/
theorem rootXYUpdate_mul_defect (X Y : OpZornMatrix A) :
    rootXYUpdate (X * Y) - rootXYUpdate X * rootXYUpdate Y =
      -(rootXY X * rootXY Y) := by
  ext <;>
    simp [rootXYUpdate, rootXY, OpVec3.dot, OpVec3.skewCross,
      OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale,
      OpZornMatrix.mul_a, OpZornMatrix.mul_v,
      OpZornMatrix.mul_w, OpZornMatrix.mul_b, rootXY_leibniz] <;>
    noncomm_ring

/-- The image of `rootXY` has upper support on the x-axis and lower support
on the y-axis. These supports are orthogonal for the owner's dot and
skew-cross operations, so products of two image elements vanish. -/
theorem rootXY_mul_zero (X Y : OpZornMatrix A) :
    rootXY X * rootXY Y = 0 := by
  ext <;>
    simp [rootXY, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale]

/-- The root update is multiplicative because its quadratic defect vanishes. -/
theorem rootXYUpdate_mul (X Y : OpZornMatrix A) :
    rootXYUpdate (X * Y) = rootXYUpdate X * rootXYUpdate Y := by
  have h := rootXYUpdate_mul_defect X Y
  have hz : rootXY X * rootXY Y = 0 := rootXY_mul_zero X Y
  rw [hz] at h
  have h' : rootXYUpdate (X * Y) - rootXYUpdate X * rootXYUpdate Y = 0 := by
    simpa using h
  exact sub_eq_zero.mp h'

/-- The root action is square-zero, hence `id - rootXY` is a two-sided
inverse of the terminated update `id + rootXY`. -/
theorem rootXY_sq (X : OpZornMatrix A) : rootXY (rootXY X) = 0 := by
  ext <;> simp [rootXY]

def rootXYUpdateInv (X : OpZornMatrix A) : OpZornMatrix A := X - rootXY X

theorem rootXYUpdate_left_inverse (X : OpZornMatrix A) :
    rootXYUpdateInv (rootXYUpdate X) = X := by
  ext <;> simp [rootXYUpdateInv, rootXYUpdate, rootXY] <;> abel

theorem rootXYUpdate_right_inverse (X : OpZornMatrix A) :
    rootXYUpdate (rootXYUpdateInv X) = X := by
  ext <;> simp [rootXYUpdateInv, rootXYUpdate, rootXY] <;> abel

theorem rootXYUpdate_add (X Y : OpZornMatrix A) :
    rootXYUpdate (X + Y) = rootXYUpdate X + rootXYUpdate Y := by
  ext <;> simp [rootXYUpdate, rootXY] <;> abel

theorem rootXYUpdate_one : rootXYUpdate (1 : OpZornMatrix A) = 1 := by
  ext <;> simp [rootXYUpdate, rootXY]

theorem rootXYUpdate_bijective : Function.Bijective (rootXYUpdate (A := A)) := by
  constructor
  · intro X Y h
    calc
      X = rootXYUpdateInv (rootXYUpdate X) := (rootXYUpdate_left_inverse X).symm
      _ = rootXYUpdateInv (rootXYUpdate Y) := congrArg rootXYUpdateInv h
      _ = Y := rootXYUpdate_left_inverse Y
  · intro Y
    exact ⟨rootXYUpdateInv Y, rootXYUpdate_right_inverse Y⟩

theorem rootZX_leibniz (X Y : OpZornMatrix A) :
    rootZX (X * Y) = rootZX X * Y + X * rootZX Y := by
  ext <;>
    simp [rootZX, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    (first | noncomm_ring | abel)

theorem rootZX_mul_zero (X Y : OpZornMatrix A) : rootZX X * rootZX Y = 0 := by
  ext <;> simp [rootZX, OpVec3.dot, OpVec3.skewCross,
    OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

def rootZXUpdate (X : OpZornMatrix A) := X + rootZX X

theorem rootZXUpdate_mul (X Y : OpZornMatrix A) :
    rootZXUpdate (X * Y) = rootZXUpdate X * rootZXUpdate Y := by
  ext <;> simp [rootZXUpdate, rootZX, OpVec3.dot, OpVec3.skewCross,
    OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale] <;> noncomm_ring

/-- The next cyclic contragredient root, with upper support on `y` and
dual lower support on `z`. -/
def rootYZ (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨0, ⟨0, X.v.z, 0⟩, ⟨0, 0, -X.w.y⟩, 0⟩

def rootYZUpdate (X : OpZornMatrix A) : OpZornMatrix A := X + rootYZ X

theorem rootYZ_leibniz (X Y : OpZornMatrix A) :
    rootYZ (X * Y) = rootYZ X * Y + X * rootYZ Y := by
  ext <;>
    simp [rootYZ, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    (first | noncomm_ring | abel)

theorem rootYZ_mul_zero (X Y : OpZornMatrix A) : rootYZ X * rootYZ Y = 0 := by
  ext <;> simp [rootYZ, OpVec3.dot, OpVec3.skewCross,
    OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

theorem rootYZUpdate_mul (X Y : OpZornMatrix A) :
    rootYZUpdate (X * Y) = rootYZUpdate X * rootYZUpdate Y := by
  ext <;>
    simp [rootYZUpdate, rootYZ, OpVec3.dot, OpVec3.skewCross,
      OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

theorem rootYZ_sq (X : OpZornMatrix A) : rootYZ (rootYZ X) = 0 := by
  ext <;> simp [rootYZ]

def rootYZUpdateInv (X : OpZornMatrix A) : OpZornMatrix A := X - rootYZ X

theorem rootYZUpdate_left_inverse (X : OpZornMatrix A) :
    rootYZUpdateInv (rootYZUpdate X) = X := by
  ext <;> simp [rootYZUpdateInv, rootYZUpdate, rootYZ] <;> abel

theorem rootYZUpdate_right_inverse (X : OpZornMatrix A) :
    rootYZUpdate (rootYZUpdateInv X) = X := by
  ext <;> simp [rootYZUpdateInv, rootYZUpdate, rootYZ] <;> abel

theorem rootYZUpdate_add (X Y : OpZornMatrix A) :
    rootYZUpdate (X + Y) = rootYZUpdate X + rootYZUpdate Y := by
  ext <;> simp [rootYZUpdate, rootYZ] <;> abel

theorem rootYZUpdate_one : rootYZUpdate (1 : OpZornMatrix A) = 1 := by
  ext <;> simp [rootYZUpdate, rootYZ]

theorem rootYZUpdate_bijective : Function.Bijective (rootYZUpdate (A := A)) := by
  constructor
  · intro X Y h
    calc
      X = rootYZUpdateInv (rootYZUpdate X) := (rootYZUpdate_left_inverse X).symm
      _ = rootYZUpdateInv (rootYZUpdate Y) := congrArg rootYZUpdateInv h
      _ = Y := rootYZUpdate_left_inverse Y
  · intro Y
    exact ⟨rootYZUpdateInv Y, rootYZUpdate_right_inverse Y⟩

/-- The three roots opposite to `rootXY`, `rootYZ`, and `rootZX`. -/
def rootYX (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨0, ⟨0, X.v.x, 0⟩, ⟨-X.w.y, 0, 0⟩, 0⟩

def rootZY (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨0, ⟨0, 0, X.v.y⟩, ⟨0, -X.w.z, 0⟩, 0⟩

def rootXZ (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨0, ⟨X.v.z, 0, 0⟩, ⟨0, 0, -X.w.x⟩, 0⟩

theorem rootYX_leibniz (X Y : OpZornMatrix A) :
    rootYX (X * Y) = rootYX X * Y + X * rootYX Y := by
  ext <;>
    simp [rootYX, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    (first | noncomm_ring | abel)

theorem rootZY_leibniz (X Y : OpZornMatrix A) :
    rootZY (X * Y) = rootZY X * Y + X * rootZY Y := by
  ext <;>
    simp [rootZY, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    (first | noncomm_ring | abel)

theorem rootXZ_leibniz (X Y : OpZornMatrix A) :
    rootXZ (X * Y) = rootXZ X * Y + X * rootXZ Y := by
  ext <;>
    simp [rootXZ, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    (first | noncomm_ring | abel)

theorem rootYX_mul_zero (X Y : OpZornMatrix A) : rootYX X * rootYX Y = 0 := by
  ext <;> simp [rootYX, OpVec3.dot, OpVec3.skewCross,
    OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

theorem rootZY_mul_zero (X Y : OpZornMatrix A) : rootZY X * rootZY Y = 0 := by
  ext <;> simp [rootZY, OpVec3.dot, OpVec3.skewCross,
    OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

theorem rootXZ_mul_zero (X Y : OpZornMatrix A) : rootXZ X * rootXZ Y = 0 := by
  ext <;> simp [rootXZ, OpVec3.dot, OpVec3.skewCross,
    OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale]

def rootYXUpdate (X : OpZornMatrix A) := X + rootYX X
def rootZYUpdate (X : OpZornMatrix A) := X + rootZY X
def rootXZUpdate (X : OpZornMatrix A) := X + rootXZ X

theorem rootXZ_sq (X : OpZornMatrix A) : rootXZ (rootXZ X) = 0 := by
  ext <;> simp [rootXZ]

def rootXZUpdateInv (X : OpZornMatrix A) := X - rootXZ X

theorem rootXZUpdate_left_inverse (X : OpZornMatrix A) :
    rootXZUpdateInv (rootXZUpdate X) = X := by
  ext <;> simp [rootXZUpdateInv, rootXZUpdate, rootXZ] <;> abel

theorem rootXZUpdate_right_inverse (X : OpZornMatrix A) :
    rootXZUpdate (rootXZUpdateInv X) = X := by
  ext <;> simp [rootXZUpdateInv, rootXZUpdate, rootXZ] <;> abel

theorem rootXZUpdate_add (X Y : OpZornMatrix A) :
    rootXZUpdate (X + Y) = rootXZUpdate X + rootXZUpdate Y := by
  ext <;> simp [rootXZUpdate, rootXZ] <;> abel

theorem rootXZUpdate_one : rootXZUpdate (1 : OpZornMatrix A) = 1 := by
  ext <;> simp [rootXZUpdate, rootXZ]

theorem rootXZUpdate_bijective : Function.Bijective (rootXZUpdate (A := A)) := by
  constructor
  · intro X Y h
    calc
      X = rootXZUpdateInv (rootXZUpdate X) := (rootXZUpdate_left_inverse X).symm
      _ = rootXZUpdateInv (rootXZUpdate Y) := congrArg rootXZUpdateInv h
      _ = Y := rootXZUpdate_left_inverse Y
  · intro Y
    exact ⟨rootXZUpdateInv Y, rootXZUpdate_right_inverse Y⟩

/-- The elementary group commutator of the two simple positive root updates
is the `x <- z` update. The statement is about composition of maps; it does
not assume associativity of the ambient Zorn multiplication. -/
theorem root_updates_group_commutator (X : OpZornMatrix A) :
    rootXYUpdate (rootYZUpdate (rootXYUpdateInv (rootYZUpdateInv X))) =
      rootXZUpdate X := by
  ext <;>
    simp [rootXYUpdate, rootYZUpdate, rootXYUpdateInv, rootYZUpdateInv,
      rootXY, rootYZ, rootXZUpdate, rootXZ] <;>
    (first | abel | rfl)

theorem rootYXUpdate_mul (X Y : OpZornMatrix A) :
    rootYXUpdate (X * Y) = rootYXUpdate X * rootYXUpdate Y := by
  ext <;> simp [rootYXUpdate, rootYX, OpVec3.dot, OpVec3.skewCross,
    OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale] <;> noncomm_ring

theorem rootZYUpdate_mul (X Y : OpZornMatrix A) :
    rootZYUpdate (X * Y) = rootZYUpdate X * rootZYUpdate Y := by
  ext <;> simp [rootZYUpdate, rootZY, OpVec3.dot, OpVec3.skewCross,
    OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale] <;> noncomm_ring

theorem rootXZUpdate_mul (X Y : OpZornMatrix A) :
    rootXZUpdate (X * Y) = rootXZUpdate X * rootXZUpdate Y := by
  ext <;> simp [rootXZUpdate, rootXZ, OpVec3.dot, OpVec3.skewCross,
    OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale] <;> noncomm_ring

theorem six_root_actions_are_derivations_and_updates_multiplicative
    (X Y : OpZornMatrix A) :
    rootXY (X * Y) = rootXY X * Y + X * rootXY Y ∧
    rootYZ (X * Y) = rootYZ X * Y + X * rootYZ Y ∧
    rootYX (X * Y) = rootYX X * Y + X * rootYX Y ∧
    rootZY (X * Y) = rootZY X * Y + X * rootZY Y ∧
    rootZX (X * Y) = rootZX X * Y + X * rootZX Y ∧
    rootXZ (X * Y) = rootXZ X * Y + X * rootXZ Y ∧
    rootXY X * rootXY Y = 0 ∧ rootYZ X * rootYZ Y = 0 ∧
    rootYX X * rootYX Y = 0 ∧ rootZY X * rootZY Y = 0 ∧
    rootZX X * rootZX Y = 0 ∧ rootXZ X * rootXZ Y = 0 ∧
    rootXYUpdate (X * Y) = rootXYUpdate X * rootXYUpdate Y ∧
    rootYZUpdate (X * Y) = rootYZUpdate X * rootYZUpdate Y ∧
    rootZXUpdate (X * Y) = rootZXUpdate X * rootZXUpdate Y ∧
    rootYXUpdate (X * Y) = rootYXUpdate X * rootYXUpdate Y ∧
    rootZYUpdate (X * Y) = rootZYUpdate X * rootZYUpdate Y ∧
    rootXZUpdate (X * Y) = rootXZUpdate X * rootXZUpdate Y := by
  exact ⟨rootXY_leibniz X Y, rootYZ_leibniz X Y,
    rootYX_leibniz X Y, rootZY_leibniz X Y, rootZX_leibniz X Y,
    rootXZ_leibniz X Y,
    rootXY_mul_zero X Y, rootYZ_mul_zero X Y,
    rootYX_mul_zero X Y, rootZY_mul_zero X Y, rootZX_mul_zero X Y,
    rootXZ_mul_zero X Y,
    rootXYUpdate_mul X Y, rootYZUpdate_mul X Y,
    rootZXUpdate_mul X Y, rootYXUpdate_mul X Y, rootZYUpdate_mul X Y,
    rootXZUpdate_mul X Y⟩

/-- Triality cycles the three positive root actions of the owner algebra. -/
theorem triality_rootXY (X : OpZornMatrix A) :
    zornGaloisZ3 (rootXY X) = rootZX (zornGaloisZ3 X) := by
  ext <;> simp [zornGaloisZ3, OpVec3.trialityPerm, rootXY, rootZX]

theorem triality_rootZX (X : OpZornMatrix A) :
    zornGaloisZ3 (rootZX X) = rootYZ (zornGaloisZ3 X) := by
  ext <;> simp [zornGaloisZ3, OpVec3.trialityPerm, rootZX, rootYZ]

theorem triality_rootYZ (X : OpZornMatrix A) :
    zornGaloisZ3 (rootYZ X) = rootXY (zornGaloisZ3 X) := by
  ext <;> simp [zornGaloisZ3, OpVec3.trialityPerm, rootYZ, rootXY]

/-- Triality also intertwines the corresponding unipotent updates. -/
theorem triality_rootXYUpdate (X : OpZornMatrix A) :
    zornGaloisZ3 (rootXYUpdate X) = rootZXUpdate (zornGaloisZ3 X) := by
  ext <;> simp [rootXYUpdate, rootZXUpdate, zornGaloisZ3,
    OpVec3.trialityPerm, rootXY, rootZX] <;> abel

theorem triality_rootZXUpdate (X : OpZornMatrix A) :
    zornGaloisZ3 (rootZXUpdate X) = rootYZUpdate (zornGaloisZ3 X) := by
  ext <;> simp [rootZXUpdate, rootYZUpdate, zornGaloisZ3,
    OpVec3.trialityPerm, rootZX, rootYZ] <;> abel

theorem triality_rootYZUpdate (X : OpZornMatrix A) :
    zornGaloisZ3 (rootYZUpdate X) = rootXYUpdate (zornGaloisZ3 X) := by
  ext <;> simp [rootYZUpdate, rootXYUpdate, zornGaloisZ3,
    OpVec3.trialityPerm, rootYZ, rootXY] <;> abel

/-- The commutator of the two simple root endomorphisms is the composite
root action `x <- z`, with its contragredient action on the lower vector. -/
theorem rootXY_rootYZ_commutator (X : OpZornMatrix A) :
    rootXY (rootYZ X) - rootYZ (rootXY X) = rootXZ X := by
  ext <;> simp [rootXY, rootYZ, rootXZ]

end InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
