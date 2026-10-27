/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ZornRootUnipotentObstruction

/-!
# Signed Weyl maps from the owner Zorn root updates

The carrier and multiplication are imported from `AlbertCayleyDickson`.
These maps are the coordinate actions of the Steinberg triples built from
the owner root updates.  The coordinate identities hold over every ring;
distinctness of all 24 signed permutations needs an extra hypothesis such
as `1 ≠ -1`.
-/

namespace InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion

variable {A : Type*} [Ring A]

/-- Signed transposition in the `x,y` plane, acting identically on the
upper and lower vector coordinates. -/
def weylXY (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.a, ⟨X.v.y, -X.v.x, X.v.z⟩, ⟨X.w.y, -X.w.x, X.w.z⟩, X.b⟩

/-- Signed transposition in the `y,z` plane. -/
def weylYZ (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.a, ⟨X.v.x, X.v.z, -X.v.y⟩, ⟨X.w.x, X.w.z, -X.w.y⟩, X.b⟩

/-- Signed transposition in the `z,x` plane. -/
def weylZX (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.a, ⟨-X.v.z, X.v.y, X.v.x⟩, ⟨-X.w.z, X.w.y, X.w.x⟩, X.b⟩

/-- Opposite signed transposition, used as the inverse of `weylXY`. -/
def weylYX (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.a, ⟨-X.v.y, X.v.x, X.v.z⟩, ⟨-X.w.y, X.w.x, X.w.z⟩, X.b⟩

/-- Opposite signed transposition, used as the inverse of `weylYZ`. -/
def weylZY (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.a, ⟨X.v.x, -X.v.z, X.v.y⟩, ⟨X.w.x, -X.w.z, X.w.y⟩, X.b⟩

/-- Opposite signed transposition, used as the inverse of `weylZX`. -/
def weylXZ (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.a, ⟨X.v.z, X.v.y, -X.v.x⟩, ⟨X.w.z, X.w.y, -X.w.x⟩, X.b⟩

theorem weylXY_mul (X Y : OpZornMatrix A) :
    weylXY (X * Y) = weylXY X * weylXY Y := by
  ext <;>
    simp [weylXY, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    (first | noncomm_ring | abel)

theorem weylYZ_mul (X Y : OpZornMatrix A) :
    weylYZ (X * Y) = weylYZ X * weylYZ Y := by
  ext <;>
    simp [weylYZ, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    (first | noncomm_ring | abel)

theorem weylZX_mul (X Y : OpZornMatrix A) :
    weylZX (X * Y) = weylZX X * weylZX Y := by
  ext <;>
    simp [weylZX, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    (first | noncomm_ring | abel)

theorem weylXY_inverse_laws (X : OpZornMatrix A) :
    weylXY (weylYX X) = X ∧ weylYX (weylXY X) = X := by
  constructor <;> ext <;> simp [weylXY, weylYX]

theorem weylYZ_inverse_laws (X : OpZornMatrix A) :
    weylYZ (weylZY X) = X ∧ weylZY (weylYZ X) = X := by
  constructor <;> ext <;> simp [weylYZ, weylZY]

theorem weylZX_inverse_laws (X : OpZornMatrix A) :
    weylZX (weylXZ X) = X ∧ weylXZ (weylZX X) = X := by
  constructor <;> ext <;> simp [weylZX, weylXZ]

/-- The three cyclic products are the owner triality map.  The order shown
is function composition: the rightmost Weyl map acts first. -/
theorem weyl_cyclic_products_are_triality (X : OpZornMatrix A) :
    weylYZ (weylXY X) = zornGaloisZ3 X ∧
    weylZX (weylYZ X) = zornGaloisZ3 X ∧
    weylXY (weylZX X) = zornGaloisZ3 X := by
  constructor
  · ext <;> simp [weylXY, weylYZ, zornGaloisZ3, OpVec3.trialityPerm]
  constructor
  · ext <;> simp [weylYZ, weylZX, zornGaloisZ3, OpVec3.trialityPerm]
  · ext <;> simp [weylZX, weylXY, zornGaloisZ3, OpVec3.trialityPerm]

/-- The Coxeter braid relation for the two simple signed transpositions. -/
theorem weyl_artin_braid (X : OpZornMatrix A) :
    weylXY (weylYZ (weylXY X)) = weylYZ (weylXY (weylYZ X)) := by
  ext <;> simp [weylXY, weylYZ]

/-- Squares of signed transpositions are the corresponding sign flips. -/
theorem weyl_squares_are_klein (X : OpZornMatrix A) :
    weylYZ (weylYZ X) = zornKleinX X ∧
    weylZX (weylZX X) = zornKleinY X ∧
    weylXY (weylXY X) = zornKleinZ X := by
  constructor
  · ext <;> simp [weylYZ, zornKleinX, zornGradeParity,
      OpVec3.gradeParity]
  constructor
  · ext <;> simp [weylZX, zornKleinY, zornGradeParity,
      OpVec3.gradeParity, OpVec3.kleinY]
  · ext <;> simp [weylXY, zornKleinZ, zornGradeParity,
      OpVec3.gradeParity, OpVec3.kleinZ]

/-- The signed maps are distinct when `1 ≠ -1`; without that condition
they can collapse (in particular, in characteristic two). -/
theorem weylXY_ne_weylYX_of_one_ne_neg_one
    (hchar : (1 : A) ≠ -1) : weylXY (A := A) ≠ weylYX := by
  intro h
  have hcoord : (1 : A) = -1 := by
    simpa [weylXY, weylYX] using
      congrArg (fun Y : OpZornMatrix A => Y.v.x)
        (congrFun h ⟨0, ⟨0, 1, 0⟩, 0, 0⟩)
  exact hchar hcoord

end InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
