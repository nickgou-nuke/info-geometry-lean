/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.AlbertCayleyDickson

/-!
# A verified root derivation of the owner Zorn algebra

The carrier and product are imported from `AlbertCayleyDickson`.  This file
records one canonical contragredient root action.  It does not assert that
these actions exhaust all derivations of the algebra.
-/

namespace InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion

variable {A : Type*} [Ring A]

/-- The elementary root action on the vector coordinates, with the dual
action on the opposite vector. -/
def rootXY (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨0, ⟨X.v.y, 0, 0⟩, ⟨0, -X.w.x, 0⟩, 0⟩

/-- Leibniz rule for this root action on the owner's noncommutative Zorn
product. -/
theorem rootXY_leibniz (X Y : OpZornMatrix A) :
    rootXY (X * Y) = rootXY X * Y + X * rootXY Y := by
  ext <;>
    simp [rootXY, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    (first | noncomm_ring | abel)

/-- The total vector weight acts by `+1` on the upper vector and `-1` on
the lower vector. -/
def totalVectorWeight (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨0, X.v, -X.w, 0⟩

/-- Its Leibniz defect is precisely three copies of the two skew-cross
terms. Thus this weight is not generally a derivation; in characteristic
three this particular obstruction vanishes. -/
theorem totalVectorWeight_defect (X Y : OpZornMatrix A) :
    totalVectorWeight (X * Y) -
        (totalVectorWeight X * Y + X * totalVectorWeight Y) =
      ⟨0,
        -(OpVec3.skewCross X.w Y.w + OpVec3.skewCross X.w Y.w +
          OpVec3.skewCross X.w Y.w),
        -(OpVec3.skewCross X.v Y.v + OpVec3.skewCross X.v Y.v +
          OpVec3.skewCross X.v Y.v),
        0⟩ := by
  ext <;>
    simp [totalVectorWeight, OpVec3.dot, OpVec3.skewCross,
      OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale] <;>
    (first | noncomm_ring | abel)

end InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
