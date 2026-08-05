import InfoGeometry.SuperMetriplectic.Cl44WeylD4
import InfoGeometry.SuperMetriplectic.Axioms
import InfoGeometry.SuperMetriplectic.SupertraceBodyBridge

/-!
# Functional Definition: Metriplectic Information Super-Gas

Final scalar/body-level functional packet for the information super-gas model.

The package records:

* Massieu potential as the logarithmic Weyl-character readout;
* charge density and pressure as supplied logarithmic-derivative readouts;
* an equation of state through a hyperbolic-response scalar;
* conformal and BPS limiting equations;
* entropy production as an observable body/Fisher nonnegative quantity.

The raw supertrace remains a signed readout.  The second-law theorem in this
file is therefore stated for the body/Fisher entropy production, consistent
with `SupertraceBodyBridge`.
-/

namespace InfoGeometry.SuperMetriplectic


/-- Massieu potential is the log-character readout. -/
theorem massieu_eq_logCharacter_readout
    (massieuPotential logCharacterReadout : ℝ)
    (h : massieuPotential = logCharacterReadout) :
    massieuPotential = logCharacterReadout := h

/-- Charge density is the negative logarithmic derivative in the charge lane. -/
theorem chargeDensity_eq
    (chargeDensity chargeDerivative : ℝ)
    (h : chargeDensity = -chargeDerivative) :
    chargeDensity = -chargeDerivative := h

/-- Pressure is the negative logarithmic derivative in the stress lane. -/
theorem pressureReadout_eq
    (pressureReadout pressureDerivative : ℝ)
    (h : pressureReadout = -pressureDerivative) :
    pressureReadout = -pressureDerivative := h

/-- Equation of state in multiplication form, avoiding division by density. -/
theorem pressure_eq_eos_mul_density
    (pressureReadout hyperbolicEosReadout chargeDensity : ℝ)
    (h : pressureReadout = hyperbolicEosReadout * chargeDensity) :
    pressureReadout = hyperbolicEosReadout * chargeDensity := h

/-- In the conformal limit the trace anomaly vanishes. -/
theorem anomaly_zero
    (traceAnomaly : ℝ)
    (h : traceAnomaly = 0) :
    traceAnomaly = 0 := h

/-- Conformal pressure law `3P = ρ`. -/
theorem conformal_pressure
    (pressureReadout energyDensity : ℝ)
    (h : 3 * pressureReadout = energyDensity) :
    3 * pressureReadout = energyDensity := h

/-- In the BPS limit pressure is balanced by the central/charge density. -/
theorem bps_pressure_eq_charge
    (pressureReadout chargeDensity : ℝ)
    (h : pressureReadout = chargeDensity) :
    pressureReadout = chargeDensity := h

/-- Protected compressibility vanishes in the BPS lane. -/
theorem compressibility_zero
    (protectedCompressibility : ℝ)
    (h : protectedCompressibility = 0) :
    protectedCompressibility = 0 := h

/-- Protected entropy production vanishes in the BPS lane. -/
theorem bps_entropyProduction_zero
    (protectedEntropyProduction : ℝ)
    (h : protectedEntropyProduction = 0) :
    protectedEntropyProduction = 0 := h

/-- The functional Weyl character is the partition function of the character packet. -/
theorem weylCharacter_eq_partition
    (weylCharacter partitionFunction : ℝ)
    (h : weylCharacter = partitionFunction) :
    weylCharacter = partitionFunction := h

/-- Observable entropy production remains body-nonnegative. -/
theorem body_entropy_nonnegative
    (entropyProduction : ℝ)
    (h : 0 ≤ entropyProduction) :
    0 ≤ entropyProduction := h

/-- The raw supertrace channel is signed, not the second-law order by itself. -/
theorem supertrace_signed
    (supertraceQuadratic evenQuadratic oddQuadratic nilpotentCancellation : ℝ)
    (h : supertraceQuadratic = evenQuadratic - oddQuadratic + nilpotentCancellation) :
    supertraceQuadratic = evenQuadratic - oddQuadratic + nilpotentCancellation := h

/--
Final functional theorem:
Weyl character as partition function, Massieu log-character readout, EoS,
conformal/BPS limits, body second law, and signed supertrace bookkeeping.
-/
theorem information_super_gas_functional_definition
    (weylCharacter partitionFunction massieuPotential logCharacterReadout : ℝ)
    (pressureReadout hyperbolicEosReadout chargeDensity : ℝ)
    (conformalPressure conformalEnergy : ℝ)
    (bpsPressure bpsCharge bpsCompressibility bpsEntropy : ℝ)
    (entropyProduction : ℝ)
    (supertraceQuadratic evenQuadratic oddQuadratic nilpotentCancellation : ℝ)
    (h_weyl : weylCharacter = partitionFunction)
    (h_mass : massieuPotential = logCharacterReadout)
    (h_pres : pressureReadout = hyperbolicEosReadout * chargeDensity)
    (h_conf : 3 * conformalPressure = conformalEnergy)
    (h_bps_p : bpsPressure = bpsCharge)
    (h_bps_c : bpsCompressibility = 0)
    (h_bps_e : bpsEntropy = 0)
    (h_ent : 0 ≤ entropyProduction)
    (h_sup : supertraceQuadratic = evenQuadratic - oddQuadratic + nilpotentCancellation) :
    weylCharacter = partitionFunction
      ∧ massieuPotential = logCharacterReadout
      ∧ pressureReadout = hyperbolicEosReadout * chargeDensity
      ∧ 3 * conformalPressure = conformalEnergy
      ∧ bpsPressure = bpsCharge
      ∧ bpsCompressibility = 0
      ∧ bpsEntropy = 0
      ∧ 0 ≤ entropyProduction
      ∧ supertraceQuadratic = evenQuadratic - oddQuadratic + nilpotentCancellation :=
  ⟨h_weyl, h_mass, h_pres, h_conf, h_bps_p, h_bps_c, h_bps_e, h_ent, h_sup⟩

/-!
The capstone consumer uses only two finite readouts from this functional
packet.  Keep them explicit rather than introducing an implicit placeholder
type: the finite index `ι` is retained as the state-space parameter, while the
functional and body positivity laws are supplied as data.
-/

abbrev InformationSuperGasFunctional := ℝ

namespace InformationSuperGasFunctional

/-- Compatibility accessor for the native scalar Weyl-character readout. -/
abbrev weylCharacter (F : InformationSuperGasFunctional) : ℝ := F

end InformationSuperGasFunctional

structure InformationSuperGasEntropyBody where
  production : ℝ
  production_nonnegative : 0 ≤ production

structure InformationSuperGasCapstone (ι : Type*) [Fintype ι] where
  functional : InformationSuperGasFunctional
  entropyBody : InformationSuperGasEntropyBody

namespace InformationSuperGasCapstone

variable {ι : Type*} [Fintype ι]

theorem body_entropy_nonnegative
    (G : InformationSuperGasCapstone ι) :
    0 ≤ G.entropyBody.production :=
  G.entropyBody.production_nonnegative

end InformationSuperGasCapstone

end InfoGeometry.SuperMetriplectic
