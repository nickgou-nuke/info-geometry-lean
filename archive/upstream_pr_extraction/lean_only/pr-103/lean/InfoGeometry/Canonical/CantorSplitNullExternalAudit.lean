import InfoGeometry.Canonical.CantorSplitNullBridge

/-!
# Native finite Cantor split-null identities

This owner contains only kernel-checked identities for the finite Cantor
split-null construction. External tool status is not part of the Lean model.
-/

namespace InfoGeometry.Canonical.CantorSplitNullExternalAudit

open InfoGeometry.Canonical.CantorSplitNullBridge
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

theorem child_false_detZ_zero
    (w : List Bool) :
    detZ (addressNullGenerator
      (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w false)) = 0 := by
  simpa using addressNullGenerator_child_detZ_zero w false

theorem child_true_detZ_zero
    (w : List Bool) :
    detZ (addressNullGenerator
      (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w true)) = 0 := by
  simpa using addressNullGenerator_child_detZ_zero w true

theorem child_false_true_polar_pair
    (w : List Bool) :
    polarZ
      (addressNullGenerator
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w false))
      (addressNullGenerator
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w true)) = -1 := by
  simpa using InfoGeometry.Canonical.CantorSplitNullBridge.child_false_true_polar_pair w

end InfoGeometry.Canonical.CantorSplitNullExternalAudit
