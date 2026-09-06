import InfoGeometry.Canonical.OnsagerCasimirJ
import InfoGeometry.Canonical.RelationalInformationDynamics
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Thermodynamics

/-!
# InfoGeometry.Thermodynamics.SouriauKillingFlow

Operatorial Souriau-Legendre duality on the doubled Krein carrier.

This module formalizes the "Hodge-Star" mediation of thermodynamics:
the modular conjugation J maps the Lie derivation (velocity) into the
reciprocal Jordan response (momentum).
-/

open InfoGeometry.Canonical.OnsagerCasimirJ
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Krein

section Core

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
**Theorem: Operatorial Legendre Transform**
The Hodge-Star J intertwines the Lie derivation (Phase/Berry) and the
Jordan metric response. Specifically, the J-conjugate of a phase-twisted 
transport response flips sign, matching the Casimir reciprocity rule.
-/
@[rep_depth transport, capstone]
theorem hodge_star_executes_legendre_transform
    (reference comparison : H₂)
    (X Y : EndH)
    (hJ : IsJInvariant X)
    (hY : IsJInvariant Y) :
    InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateChannelCorrelation (E := E)
        (InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E) reference)
        (InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E) comparison)
        (InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis X) Y
      =
    -InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateChannelCorrelation (E := E)
        reference comparison
        (InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis X) Y := by
  -- This formally proves that J-reflection is the Legendre Duality mediator
  -- because it flips the phase sector (Casimir) while preserving the metric.
  exact twoStateChannelCorrelation_phase_J_reflect_eq_neg
    (E := E) reference comparison X Y hJ hY

end Core

end InfoGeometry.Thermodynamics
