import InfoGeometry.Canonical.SouriauThermodynamics
import InfoGeometry.Canonical.SouriauTomitaModularFlowBridge
import InfoGeometry.Thermo.RelativeTemperatureFirstLaw
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.SouriauRelativeTemperatureBridge

Trace-free Souriau scalar temperature bridge.

This file keeps the Souriau side split into two honest lanes:

* `GeometricTemperature.beta` is the scalar inverse-temperature scale;
* `RelativeTemperatureDatum` carries the finite scalar first law;
* no trace is introduced for type-III/operatorial lanes;
* the operatorial Tomita lane reuses the owned `Delta` / modular Hamiltonian
  / thermal-generator readbacks.

The operatorial modular generator remains separate from scalar `β`.
-/

noncomputable section

namespace SouriauRelativeTemperatureBridge

open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.Thermo.RelativeTemperatureFirstLaw

/-! ## Calibration packet -/

/--
Souriau scalar temperature calibration.

This packages a Souriau geometric temperature together with the scalar
relative-temperature datum that reads it as an inverse scale.
-/
@[rep_depth thermo]
structure SouriauFirstLawCalibration where
  souriauTemperature : GeometricTemperature
  firstLaw : RelativeTemperatureDatum
  beta_eq : firstLaw.β = souriauTemperature.beta

namespace SouriauFirstLawCalibration

variable (C : SouriauFirstLawCalibration)

/-- The scalar temperature is the inverse Souriau beta scale. -/
@[rep_depth thermo]
theorem temperature_eq_inv_beta :
    C.firstLaw.T = C.souriauTemperature.beta⁻¹ := by
  rw [← C.beta_eq, C.firstLaw.temperature_eq_inv_beta]

/-- The reversible first law in Souriau calibration form. -/
@[rep_depth thermo]
theorem temperature_mul_entropy_eq_heat
    (hβ : C.firstLaw.β ≠ 0) :
    C.firstLaw.T * C.firstLaw.dS = C.firstLaw.dQ := by
  exact C.firstLaw.temperature_mul_entropy_eq_heat hβ

/-- Inverse-temperature readout in Souriau calibration form. -/
@[rep_depth thermo]
theorem invTemperature_eq_entropy_div_heat
    (hQ : C.firstLaw.dQ ≠ 0) :
    C.firstLaw.β = C.firstLaw.dS / C.firstLaw.dQ := by
  exact C.firstLaw.invTemperature_eq_entropy_div_heat hQ

end SouriauFirstLawCalibration

/-- Trace-free calibration tying Souriau scalar temperature to the Tomita log-context. -/
@[rep_depth thermo]
structure SouriauTomitaFirstLawCalibration
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Symmetry : Type*) where
  scalarCalibration : SouriauFirstLawCalibration
  tomitaLogContext :
    InfoGeometry.Canonical.SouriauTomitaModularFlowBridge.SouriauTomitaLogContext
      (H := E) (Symmetry := Symmetry)

namespace SouriauTomitaFirstLawCalibration

open InfoGeometry.Canonical.SouriauTomitaModularFlowBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Symmetry : Type*}
variable (C : SouriauTomitaFirstLawCalibration (E := E) Symmetry)

/-- The scalar first law still reads `T = β⁻¹` on the calibrated Souriau scale. -/
@[rep_depth thermo]
theorem temperature_eq_inv_beta :
    C.scalarCalibration.firstLaw.T = C.scalarCalibration.souriauTemperature.beta⁻¹ :=
  C.scalarCalibration.temperature_eq_inv_beta

/-- The Tomita logarithmic datum is the modular Hamiltonian. -/
@[rep_depth operator]
theorem tomitaDelta_eq_modularHamiltonian :
    C.tomitaLogContext.toRealModularLogData = C.tomitaLogContext.modularHamiltonian := by
  rfl

/-- The Tomita standard-form carrier uses the modular Hamiltonian as `Delta`. -/
@[rep_depth operator]
theorem tomitaStandardFormCarrier_eq :
    C.tomitaLogContext.toStandardFormCarrier.Delta = C.tomitaLogContext.modularHamiltonian :=
  C.tomitaLogContext.toStandardFormCarrier_Delta_eq_modularHamiltonian

/-- The modular Hamiltonian is the Souriau thermal generator. -/
@[rep_depth operator]
theorem modularHamiltonian_eq_thermalGenerator :
    C.tomitaLogContext.modularHamiltonian = C.tomitaLogContext.souriauMoment.thermalGenerator := by
  rfl

/-- The modular Hamiltonian is the Souriau moment at geometric temperature. -/
@[rep_depth operator]
theorem modularHamiltonian_eq_moment_geometricTemperature :
    C.tomitaLogContext.modularHamiltonian =
      C.tomitaLogContext.souriauMoment.momentOperator
        C.tomitaLogContext.souriauMoment.geometricTemperature :=
  C.tomitaLogContext.modularHamiltonian_eq_moment_geometricTemperature

end SouriauTomitaFirstLawCalibration

end SouriauRelativeTemperatureBridge
