import InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
import InfoGeometry.Canonical.SouriauTomitaModularFlowBridge
import InfoGeometry.Volume.ConnesCocycle

/-!
# G₂ Souriau-Tomita Bridge

This file establishes the bridge between the G₂ rank-two split Cartan parameters
and the infinite-dimensional operatorial Tomita-Takesaki flow.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2SouriauTomitaBridge

open InfoGeometry.Canonical.SouriauTomitaModularFlowBridge
open InfoGeometry.Lie.CanonicalZornG2CartanMellinBridge
open InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge
open InfoGeometry.Volume.ConnesCocycle

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A representation of the Cartan coordinate algebra into bounded operators on H.
This provides the concrete geometric moment action. -/
structure CartanMomentRepresentation (H : Type _) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  momentOperator : Cartan → AlgebraEnd H

/-- Lift the G₂ Cartan geometric temperature and moment representation into the general
Souriau geometric temperature context. -/
def toOperatorSouriauMoment (R : CartanMomentRepresentation H) (geometricTemperature : Cartan) :
    OperatorSouriauMoment (H := H) Cartan where
  momentOperator := R.momentOperator
  geometricTemperature := geometricTemperature

/-- The logarithmic modular context mapping the geometric temperature to the thermal generator. -/
def toSouriauTomitaLogContext (R : CartanMomentRepresentation H) (geometricTemperature : Cartan) :
    SouriauTomitaLogContext (H := H) (Symmetry := Cartan) :=
  toOperatorSouriauMoment R geometricTemperature

@[simp] theorem toOperatorSouriauMoment_thermalGenerator
    (R : CartanMomentRepresentation H) (geometricTemperature : Cartan) :
    (toOperatorSouriauMoment R geometricTemperature).thermalGenerator =
      R.momentOperator geometricTemperature := by
  rfl

/-- The Cartan moment representation is the modular Hamiltonian readout. -/
theorem toSouriauTomitaLogContext_modularHamiltonian
    (R : CartanMomentRepresentation H) (geometricTemperature : Cartan) :
    (toSouriauTomitaLogContext R geometricTemperature).modularHamiltonian =
      R.momentOperator geometricTemperature := by
  rfl

theorem toSouriauTomitaLogContext_modularFlow_apply
    (R : CartanMomentRepresentation H) (geometricTemperature : Cartan)
    (t : ℝ) (A : AlgebraEnd H) :
    (toSouriauTomitaLogContext R geometricTemperature).souriauAdditiveModularFlow t A =
      InfoGeometry.Krein.modular_shift (E := H)
        (R.momentOperator geometricTemperature) t A := by
  exact SouriauTomitaLogContext.souriauAdditiveModularFlow_apply_eq_modular_shift
    (toSouriauTomitaLogContext R geometricTemperature) t A

end InfoGeometry.Lie.CanonicalZornG2SouriauTomitaBridge
