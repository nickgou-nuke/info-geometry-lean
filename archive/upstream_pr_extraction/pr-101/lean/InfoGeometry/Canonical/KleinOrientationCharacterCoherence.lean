import InfoGeometry.Canonical.KleinOrientationCharacterBridge
import InfoGeometry.Canonical.KleinOrientationCharacter

/-!
# Orientation-character coherence for the native Klein presentation

The native semidirect-product orientation character and the character defined
from the presented Klein group are the same after transport through the
already proved presentation homomorphism.  This is an algebraic compatibility
statement only; no topological covering or operator-algebraic realization is
introduced.
-/

namespace InfoGeometry.Canonical.KleinOrientationCharacterCoherence

open InfoGeometry.Canonical.KleinNativeSemidirectProductBridge
open InfoGeometry.Canonical.KleinPresentedGroup

theorem orientationCharacter_comp_nativeKleinPresentationRep_eq_presented :
    InfoGeometry.Canonical.KleinOrientationCharacterBridge.orientationCharacter.comp
        nativeKleinPresentationRep =
      InfoGeometry.Canonical.KleinOrientationCharacter.orientationCharacter := by
  apply nativeKlein_hom_ext
  · change
      InfoGeometry.Canonical.KleinOrientationCharacterBridge.orientationCharacter
          (nativeKleinPresentationRep (toKlein genA)) =
        InfoGeometry.Canonical.KleinOrientationCharacter.orientationCharacter
          (toKlein genA)
    rw [(nativeKleinPresentationRep_generators).1,
      InfoGeometry.Canonical.KleinOrientationCharacterBridge.orientationCharacter_glide,
      InfoGeometry.Canonical.KleinOrientationCharacter.orientationCharacter_genA]
    rfl
    
  · change
      InfoGeometry.Canonical.KleinOrientationCharacterBridge.orientationCharacter
          (nativeKleinPresentationRep (toKlein genB)) =
        InfoGeometry.Canonical.KleinOrientationCharacter.orientationCharacter
          (toKlein genB)
    rw [(nativeKleinPresentationRep_generators).2,
      InfoGeometry.Canonical.KleinOrientationCharacterBridge.orientationCharacter_translation,
      InfoGeometry.Canonical.KleinOrientationCharacter.orientationCharacter_genB]
    rfl

theorem orientationCharacter_nativeKleinPresentationRep
    (x : InfoGeometry.Canonical.KleinPresentedGroup.KleinGroup) :
    InfoGeometry.Canonical.KleinOrientationCharacterBridge.orientationCharacter
        (nativeKleinPresentationRep x) =
      InfoGeometry.Canonical.KleinOrientationCharacter.orientationCharacter x := by
  exact congrArg
    (fun f : InfoGeometry.Canonical.KleinPresentedGroup.KleinGroup →*
      Multiplicative (ZMod 2) => f x)
    orientationCharacter_comp_nativeKleinPresentationRep_eq_presented

end InfoGeometry.Canonical.KleinOrientationCharacterCoherence
