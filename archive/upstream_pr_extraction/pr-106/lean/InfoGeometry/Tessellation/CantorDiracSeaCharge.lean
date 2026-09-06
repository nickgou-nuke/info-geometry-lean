import InfoGeometry.Tessellation.CantorDiracSeaWalk
import InfoGeometry.CondensedMatter.CliffordAtomsZ2n
import InfoGeometry.Canonical.TypeIIIModularCantorSystem

/-!
# Tessellation Cantor Dirac-sea charge

Minimal owner-side charge admissibility packet for the Cantor/binary Dirac-sea
walk.

This file reuses the repo's existing `Z2Charge` / `flipBit` bookkeeping surface
from `CondensedMatter.CliffordAtomsZ2n`. It does not claim a full super-Lie
closure theorem; it only records the primitive left/right charge laws for
binary hops.
-/

namespace InfoGeometry.Tessellation

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.CondensedMatter.CliffordAtomsZ2n

/--
Owner-side charge packet for binary Cantor hops.

The underlying walk datum remains separate. This packet stores only the
primitive laws saying how the left and right child hops transform a local `Z2`
charge assignment on finite binary addresses.
-/
def CantorDiracSeaChargePredicate
    {Op : Type*} [Ring Op]
    (walk : CantorDiracSeaWalkDatum Op (Z2Charge Bool)) : Prop :=
  (∀ w : List Bool,
    walk.charge
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w false) =
      flipBit false (walk.charge w)) ∧
  (∀ w : List Bool,
    walk.charge
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w true) =
      flipBit true (walk.charge w))

/-- A Cantor walk together with its two primitive binary charge laws. -/
abbrev CantorDiracSeaChargeDatum
    (Op : Type*) [Ring Op] :=
  {walk : CantorDiracSeaWalkDatum Op (Z2Charge Bool) //
    CantorDiracSeaChargePredicate walk}

namespace CantorDiracSeaChargeDatum

variable {Op : Type*} [Ring Op]
variable (D : CantorDiracSeaChargeDatum Op)

abbrev walk : CantorDiracSeaWalkDatum Op (Z2Charge Bool) := D.1

lemma left_charge_law :
    ∀ w : List Bool,
      D.walk.charge
          (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w false) =
        flipBit false (D.walk.charge w) := D.2.1

lemma right_charge_law :
    ∀ w : List Bool,
      D.walk.charge
          (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w true) =
        flipBit true (D.walk.charge w) := D.2.2

/-- A left binary hop flips the false-bit charge coordinate. -/
theorem leftHop_flips_false_bit
    (w : List Bool) :
    D.walk.charge
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w false)
        false = !(D.walk.charge w false) := by
  rw [D.left_charge_law]
  simp

/-- A left binary hop preserves the true-bit charge coordinate. -/
theorem leftHop_preserves_true_bit
    (w : List Bool) :
    D.walk.charge
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w false)
        true = D.walk.charge w true := by
  rw [D.left_charge_law]
  simp

/-- A right binary hop flips the true-bit charge coordinate. -/
theorem rightHop_flips_true_bit
    (w : List Bool) :
    D.walk.charge
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w true)
        true = !(D.walk.charge w true) := by
  rw [D.right_charge_law]
  simp

/-- A right binary hop preserves the false-bit charge coordinate. -/
theorem rightHop_preserves_false_bit
    (w : List Bool) :
    D.walk.charge
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w true)
        false = D.walk.charge w false := by
  rw [D.right_charge_law]
  simp

/-- Each left hop remains admissible in the underlying walk packet. -/
theorem leftHop_admissible
    (w : List Bool) :
    D.walk.admissibleLeft w :=
  D.walk.left_charge_respects w

/-- Each right hop remains admissible in the underlying walk packet. -/
theorem rightHop_admissible
    (w : List Bool) :
    D.walk.admissibleRight w :=
  D.walk.right_charge_respects w

end CantorDiracSeaChargeDatum

end InfoGeometry.Tessellation
