import Mathlib.Data.Real.Basic
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.ChiralRadiationCones

namespace InfoGeometry.Canonical.SuperKMS_Equilibrium

open InfoGeometry.Canonical.ChiralRadiationCones

/--
Supergraded algebra packet carrying even/odd sectors.
-/
@[rep_depth thermo]
structure SupergradedAlgebra where
  Even : Type*
  Odd : Type*

/--
Interaction vertex coupling even (CCR lane) and odd (CAR lane) sectors.
-/
@[rep_depth thermo]
structure SuperchargeInteractionVertex (A : SupergradedAlgebra) where
  emit : A.Even → A.Odd
  absorb : A.Odd → A.Even

/--
Super-KMS equilibrium state packet.
-/
@[rep_depth thermo]
structure SuperKMSEquilibriumState where
  beta : ℝ
  spontaneousEmission : ℝ
  stimulatedEmission : ℝ
  absorption : ℝ
  detailedBalance :
    absorption = spontaneousEmission + stimulatedEmission

/--
Constructive branch: absorption is defined from emission channels.
-/
@[rep_depth thermo]
structure ConstructiveSuperKMSEquilibriumState where
  beta : ℝ
  spontaneousEmission : ℝ
  stimulatedEmission : ℝ

@[rep_depth thermo]
def toSuperKMSEquilibriumState
    (S : ConstructiveSuperKMSEquilibriumState) : SuperKMSEquilibriumState where
  beta := S.beta
  spontaneousEmission := S.spontaneousEmission
  stimulatedEmission := S.stimulatedEmission
  absorption := S.spontaneousEmission + S.stimulatedEmission
  detailedBalance := rfl

@[rep_depth thermo]
theorem constructive_detailed_balance
    (S : ConstructiveSuperKMSEquilibriumState) :
    (toSuperKMSEquilibriumState S).absorption =
      (toSuperKMSEquilibriumState S).spontaneousEmission +
        (toSuperKMSEquilibriumState S).stimulatedEmission := rfl

/--
Stimulated-emission theorem-facing surface on the super-KMS packet.
-/
@[rep_depth thermo]
theorem stimulated_emission_from_ccr
    (S : SuperKMSEquilibriumState) :
    S.absorption = S.spontaneousEmission + S.stimulatedEmission :=
  S.detailedBalance

/--
Coupled super-KMS and chiral-mass equilibrium packet.
-/
@[rep_depth thermo]
structure SuperKMSChiralEquilibrium (A : SupergradedAlgebra) where
  state : SuperKMSEquilibriumState
  interaction : SuperchargeInteractionVertex A
  massDynamics : ChiralScatteringMass ℝ

/--
On a super-KMS/chiral equilibrium packet, the Dirac mass-term readout is stable
because `massParameter = flipRate` in the chiral packet.
-/
@[rep_depth thermo]
theorem dirac_mass_term_is_equilibrium_constant
    {A : SupergradedAlgebra}
    (E : SuperKMSChiralEquilibrium A) (ψL ψR : ℝ) :
    diracMassTerm E.massDynamics.massParameter ψL ψR =
      diracMassTerm E.massDynamics.flipRate ψL ψR := by
  simpa using diracMassTerm_eq_of_mass_eq_flipRate E.massDynamics ψL ψR

end InfoGeometry.Canonical.SuperKMS_Equilibrium
