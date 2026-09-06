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

/--
Functional equation-of-state packet for the character-generated super-gas.

`logCharacterReadout` is the scalar shadow of `log χ_{S+}(β)`.  The derivative
readouts are supplied rather than analytically derived in this layer.
-/
structure InformationSuperGasFunctional where
  weylCharacter : ℝ
  logCharacterReadout : ℝ
  massieuPotential : ℝ
  chargeDerivative : ℝ
  pressureDerivative : ℝ
  chargeDensity : ℝ
  pressureReadout : ℝ
  hyperbolicEosReadout : ℝ
  massieu_eq_logCharacter :
    massieuPotential = logCharacterReadout
  chargeDensity_eq_neg_derivative :
    chargeDensity = -chargeDerivative
  pressureReadout_eq_neg_derivative :
    pressureReadout = -pressureDerivative
  equationOfState :
    pressureReadout = hyperbolicEosReadout * chargeDensity

namespace InformationSuperGasFunctional

/-- Massieu potential is the log-character readout. -/
theorem massieu_eq_logCharacter_readout
    (G : InformationSuperGasFunctional) :
    G.massieuPotential = G.logCharacterReadout :=
  G.massieu_eq_logCharacter

/-- Charge density is the negative logarithmic derivative in the charge lane. -/
theorem chargeDensity_eq
    (G : InformationSuperGasFunctional) :
    G.chargeDensity = -G.chargeDerivative :=
  G.chargeDensity_eq_neg_derivative

/-- Pressure is the negative logarithmic derivative in the stress lane. -/
theorem pressureReadout_eq
    (G : InformationSuperGasFunctional) :
    G.pressureReadout = -G.pressureDerivative :=
  G.pressureReadout_eq_neg_derivative

/-- Equation of state in multiplication form, avoiding division by density. -/
theorem pressure_eq_eos_mul_density
    (G : InformationSuperGasFunctional) :
    G.pressureReadout = G.hyperbolicEosReadout * G.chargeDensity :=
  G.equationOfState

end InformationSuperGasFunctional

/--
Conformal limit packet.

The ultrarelativistic/conformal equation is recorded as `3P = ρ`, avoiding
division and keeping the scalar lane constructive.
-/
structure ConformalEquationOfStateLimit where
  energyDensity : ℝ
  pressureReadout : ℝ
  traceAnomaly : ℝ
  traceAnomaly_eq_zero : traceAnomaly = 0
  conformalPressureLaw : 3 * pressureReadout = energyDensity

namespace ConformalEquationOfStateLimit

/-- In the conformal limit the trace anomaly vanishes. -/
theorem anomaly_zero
    (C : ConformalEquationOfStateLimit) :
    C.traceAnomaly = 0 :=
  C.traceAnomaly_eq_zero

/-- Conformal pressure law `3P = ρ`. -/
theorem pressure
    (C : ConformalEquationOfStateLimit) :
    3 * C.pressureReadout = C.energyDensity :=
  C.conformalPressureLaw

end ConformalEquationOfStateLimit

/--
BPS limit packet.

The protected limit has pressure balanced by charge, zero protected
compressibility, and zero protected entropy production.
-/
structure BPSEquationOfStateLimit where
  chargeDensity : ℝ
  pressureReadout : ℝ
  protectedCompressibility : ℝ
  protectedEntropyProduction : ℝ
  pressure_balances_charge :
    pressureReadout = chargeDensity
  protectedCompressibility_eq_zero :
    protectedCompressibility = 0
  protectedEntropyProduction_eq_zero :
    protectedEntropyProduction = 0

namespace BPSEquationOfStateLimit

/-- In the BPS limit pressure is balanced by the central/charge density. -/
theorem pressure_eq_charge
    (B : BPSEquationOfStateLimit) :
    B.pressureReadout = B.chargeDensity :=
  B.pressure_balances_charge

/-- Protected compressibility vanishes in the BPS lane. -/
theorem compressibility_zero
    (B : BPSEquationOfStateLimit) :
    B.protectedCompressibility = 0 :=
  B.protectedCompressibility_eq_zero

/-- Protected entropy production vanishes in the BPS lane. -/
theorem entropyProduction_zero
    (B : BPSEquationOfStateLimit) :
    B.protectedEntropyProduction = 0 :=
  B.protectedEntropyProduction_eq_zero

end BPSEquationOfStateLimit

/--
Final functional capstone for the scalar/body information super-gas.
-/
structure InformationSuperGasCapstone (ι : Type*) [Fintype ι] where
  characterCapstone : WeylCharacterFormulaShadow ι
  d4Skeleton : Cl44D4CartanCharacterSkeleton
  dominantBPS : Cl44BPSDominantCharacterPacket
  functional : InformationSuperGasFunctional
  conformalLimit : ConformalEquationOfStateLimit
  bpsLimit : BPSEquationOfStateLimit
  entropyBody : BodyEntropyProduction
  supertraceShadow : SupertraceFisherShadow
  functional_character_matches_partition :
    functional.weylCharacter = characterCapstone.characterPacket.partitionFunction
  bps_skeleton_matches :
    dominantBPS.skeleton = d4Skeleton

namespace InformationSuperGasCapstone

variable {ι : Type*} [Fintype ι]

/-- The functional Weyl character is the partition function of the character packet. -/
theorem weylCharacter_eq_partition
    (C : InformationSuperGasCapstone ι) :
    C.functional.weylCharacter =
      C.characterCapstone.characterPacket.partitionFunction :=
  C.functional_character_matches_partition

/-- Functional Massieu potential is the log-character readout. -/
theorem massieu_eq_logCharacter
    (C : InformationSuperGasCapstone ι) :
    C.functional.massieuPotential = C.functional.logCharacterReadout :=
  C.functional.massieu_eq_logCharacter_readout

/-- Functional equation of state. -/
theorem pressure_eq_eos_mul_density
    (C : InformationSuperGasCapstone ι) :
    C.functional.pressureReadout =
      C.functional.hyperbolicEosReadout * C.functional.chargeDensity :=
  C.functional.pressure_eq_eos_mul_density

/-- The conformal limit carries `3P = ρ`. -/
theorem conformal_pressure
    (C : InformationSuperGasCapstone ι) :
    3 * C.conformalLimit.pressureReadout = C.conformalLimit.energyDensity :=
  C.conformalLimit.pressure

/-- The BPS limit carries `P = n`. -/
theorem bps_pressure_eq_charge
    (C : InformationSuperGasCapstone ι) :
    C.bpsLimit.pressureReadout = C.bpsLimit.chargeDensity :=
  C.bpsLimit.pressure_eq_charge

/-- Observable entropy production remains body-nonnegative. -/
theorem body_entropy_nonnegative
    (C : InformationSuperGasCapstone ι) :
    0 ≤ C.entropyBody.production :=
  C.entropyBody.body_second_law

/-- The raw supertrace channel is signed, not the second-law order by itself. -/
theorem supertrace_signed
    (C : InformationSuperGasCapstone ι) :
    C.supertraceShadow.supertraceQuadratic =
      C.supertraceShadow.evenQuadratic
        - C.supertraceShadow.oddQuadratic
        + C.supertraceShadow.nilpotentCancellation :=
  C.supertraceShadow.supertrace_eq

/--
Final functional theorem:
Weyl character as partition function, Massieu log-character readout, EoS,
conformal/BPS limits, body second law, and signed supertrace bookkeeping.
-/
theorem information_super_gas_functional_definition
    (C : InformationSuperGasCapstone ι) :
    C.functional.weylCharacter =
        C.characterCapstone.characterPacket.partitionFunction
      ∧ C.functional.massieuPotential = C.functional.logCharacterReadout
      ∧ C.functional.pressureReadout =
          C.functional.hyperbolicEosReadout * C.functional.chargeDensity
      ∧ 3 * C.conformalLimit.pressureReadout = C.conformalLimit.energyDensity
      ∧ C.bpsLimit.pressureReadout = C.bpsLimit.chargeDensity
      ∧ C.bpsLimit.protectedCompressibility = 0
      ∧ C.bpsLimit.protectedEntropyProduction = 0
      ∧ 0 ≤ C.entropyBody.production
      ∧ C.supertraceShadow.supertraceQuadratic =
          C.supertraceShadow.evenQuadratic
            - C.supertraceShadow.oddQuadratic
            + C.supertraceShadow.nilpotentCancellation := by
  exact ⟨C.weylCharacter_eq_partition,
    C.massieu_eq_logCharacter,
    C.pressure_eq_eos_mul_density,
    C.conformal_pressure,
    C.bps_pressure_eq_charge,
    C.bpsLimit.compressibility_zero,
    C.bpsLimit.entropyProduction_zero,
    C.body_entropy_nonnegative,
    C.supertrace_signed⟩

end InformationSuperGasCapstone

end InfoGeometry.SuperMetriplectic
