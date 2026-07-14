import InfoGeometry.Canonical.KleinBerryPhase
import InfoGeometry.Canonical.KleinBottleBoundaryAction
import InfoGeometry.Clifford.CliffordBott
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.KleinBerryBoundaryBottBridge

Finite bridge between the Berry-holonomy witness, the Klein boundary action,
and the Bott-periodic split Clifford carrier.

This file stays theorem-safe:

* the Berry phase data are the finite matrix witnesses already owned by
  `KleinBerryPhase`;
* the boundary action is the finite `Z₂` glide-reflection packet already owned
  by `KleinBottleBoundaryAction`;
* the Bott-periodic carrier is the repo-native direct-limit split Clifford
  algebra already owned by `CliffordBott`.

It does **not** prove a general KR-theory cascade, a global cobordism theorem,
or a K-theoretic T-duality classification.
-/

namespace KleinBerryBoundaryBottBridge

open InfoGeometry.Canonical.KleinBerryPhase
open InfoGeometry.Canonical.KleinBottleBoundaryAction
open InfoGeometry.Clifford.CliffordBott

/--
Bundle the finite Berry-holonomy witness, the finite Klein boundary action,
and the Bott-periodic nilpotent lift into one theorem-safe packet.

This is the honest topological bridge available in source:

* orientable and Klein-twisted holonomy cancellation;
* finite `Z₂` glide-reflection boundary action;
* direct-limit nilpotent lift in `Cl_infty`.
-/
@[rep_depth krein]
structure KleinBerryBoundaryBottPacket where
  orientableHolonomy :
    InfoGeometry.Canonical.KleinExceptionalBraid.B_EP *
      InfoGeometry.Canonical.KleinExceptionalBraid.B_EP = -1
  kleinHolonomy :
    InfoGeometry.Canonical.KleinExceptionalBraid.B_EP *
      (InfoGeometry.Canonical.KleinExceptionalBraid.G_Glide *
        InfoGeometry.Canonical.KleinExceptionalBraid.B_EP *
        InfoGeometry.Canonical.KleinExceptionalBraid.G_Glide) = 1
  boundaryAction : Function.Involutive KleinBoundaryCell.sheetReflection ∧
    Function.Involutive KleinBoundaryCell.deckTranslation ∧
    (∀ x : KleinBoundaryCell,
      KleinBoundaryCell.sheetReflection (KleinBoundaryCell.deckTranslation x) =
        KleinBoundaryCell.deckTranslation (KleinBoundaryCell.sheetReflection x)) ∧
    Function.Involutive KleinBoundaryCell.glideReflection
  bottLift : ∃ ε : Cl_infty, ε * ε = 0

namespace KleinBerryBoundaryBottPacket

@[rep_depth krein]
def packaged_bridge :
    InfoGeometry.Canonical.KleinBerryBoundaryBottBridge.KleinBerryBoundaryBottPacket := by
  refine
    ⟨InfoGeometry.Canonical.KleinBerryPhase.orientable_holonomy_pi,
      InfoGeometry.Canonical.KleinBerryPhase.klein_holonomy_cancellation,
      ?_,
      InfoGeometry.Clifford.CliffordBott.cl_infty_has_nilpotent_lift⟩
  exact InfoGeometry.Canonical.KleinBottleBoundaryAction.KleinBoundaryCell.finite_z2_glide_action_packet

@[rep_depth krein]
theorem boundaryAction_packet (P : KleinBerryBoundaryBottPacket) :
    Function.Involutive KleinBoundaryCell.sheetReflection ∧
      Function.Involutive KleinBoundaryCell.deckTranslation ∧
      (∀ x : KleinBoundaryCell,
        KleinBoundaryCell.sheetReflection (KleinBoundaryCell.deckTranslation x) =
          KleinBoundaryCell.deckTranslation (KleinBoundaryCell.sheetReflection x)) ∧
      Function.Involutive KleinBoundaryCell.glideReflection :=
  P.boundaryAction

@[rep_depth krein]
theorem bottLift_exists (P : KleinBerryBoundaryBottPacket) :
    ∃ ε : Cl_infty, ε * ε = 0 :=
  P.bottLift

end KleinBerryBoundaryBottPacket

end KleinBerryBoundaryBottBridge
