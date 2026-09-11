import InfoGeometry.Canonical.CStarAlgebraStateColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.HestenesKreinBilingualCarrier

/-!
# Bilingual state readouts over a filtered star-algebraic system

The analytic extension is replaced here by explicit native data: a continuous
star-inductive system, a star-algebraic cocone, and a normalized positive state
on the chosen colimit carrier.  The state restricts to a compatible family of
finite-stage states, while the Hestenes/Krein left and opposite-right actions
remain algebraic on the same carrier.

No existence of the cocone, state, or Hilbert completion is asserted.
-/

namespace InfoGeometry.Canonical.HestenesKreinBilingualStateColimitBridge

open CStarStateColimit.Native
open InfoGeometry.Physics

universe u

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable {Ainf : Type u}
variable [CStarAlgebra Ainf] [PartialOrder Ainf] [StarOrderedRing Ainf]

structure Datum where
  cocone : ContinuousStarInductiveSystem.StarInductiveCocone
    (Ainf := Ainf) Stage sys
  state : CStarStateColimit.Native.State Ainf

namespace Datum

variable (datum : Datum (Stage := Stage) (sys := sys) (Ainf := Ainf))

def compatibleStates :
    ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys :=
  ContinuousStarInductiveSystem.StarInductiveCocone.restrictStateFamily
    (Stage := Stage) (sys := sys) datum.cocone datum.state

theorem state_readout_transition
    {i j : I} (hij : i ≤ j) (a : Stage i) :
    datum.state.functional
        (datum.cocone.1 j (sys.map hij a)) =
      datum.state.functional (datum.cocone.1 i a) := by
  exact ContinuousStarInductiveSystem.StarInductiveCocone.state_readout_transition
    (Stage := Stage) (sys := sys) datum.cocone datum.state hij a

theorem bilingual_left_right_commute
    (a x : Ainf) (b : Ainfᵐᵒᵖ) :
    bilingualLeftAction a (bilingualRightOppositeAction x b) =
      bilingualRightOppositeAction (bilingualLeftAction a x) b := by
  exact InfoGeometry.Physics.bilingual_left_right_commute a x b

end Datum

end InfoGeometry.Canonical.HestenesKreinBilingualStateColimitBridge
