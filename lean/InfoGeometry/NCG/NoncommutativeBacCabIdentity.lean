/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AlbertCayleyDickson

/-!
# Ordered BAC–CAB identity over a noncommutative coefficient ring

The ordinary ordered cross product on the repository's `OpVec3` carrier does
satisfy the BAC–CAB identity over an arbitrary associative coefficient ring.
The proof retains the order of every coefficient product.  It uses the
existing operator-valued vector owner and its `naiveCross` operation.
-/

namespace InfoGeometry.NCG.NoncommutativeBacCabIdentity

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion

variable {A : Type*} [Ring A]

/-- The ordered contraction expression in the BAC–CAB identity. -/
def bacCabContraction (u w v : OpVec3 A) : OpVec3 A :=
  OpVec3.leftScale (OpVec3.dot u w) v - OpVec3.rightScale u (OpVec3.dot w v)

/-- The associator expression of the repository's ordinary ordered cross. -/
def bacCabCrossAssociator (u w v : OpVec3 A) : OpVec3 A :=
  OpVec3.naiveCross (OpVec3.naiveCross u w) v -
    OpVec3.naiveCross u (OpVec3.naiveCross w v)

/-- Noncommutative BAC–CAB: the contraction and cross expressions agree for
all operator vectors. Multiplication order is preserved throughout. -/
theorem ordered_bac_cab (u w v : OpVec3 A) :
    bacCabContraction u w v = bacCabCrossAssociator u w v := by
  ext <;>
    simp [bacCabContraction, bacCabCrossAssociator, OpVec3.dot,
      OpVec3.leftScale, OpVec3.rightScale, OpVec3.naiveCross] <;>
    noncomm_ring

end InfoGeometry.NCG.NoncommutativeBacCabIdentity
