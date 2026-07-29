/-
InfoGeometry/Arithmetic/WeylArithmeticDivergence.lean

Gauge-invariant and gauge-covariant arithmetic divergence sockets over the
projective temperature coordinate.

This module is a narrow sidecar over `ProjectiveWeylGauge` and
`ProjectivePrimePartition`.  It does not assert that KL, IS, or any zeta
readout is automatically invariant under temperature inversion.  Invariance
and covariance are supplied as witness fields and re-exported as theorem
payload.
-/

import InfoGeometry.Arithmetic.ProjectiveWeylGauge
import InfoGeometry.Arithmetic.ProjectivePrimePartition

noncomputable section

namespace InfoGeometry.Arithmetic.WeylArithmeticDivergence

open InfoGeometry.Arithmetic.PrimitiveProjectiveRays
open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.ProjectiveWeylGauge
open InfoGeometry.Arithmetic.ProjectivePrimePartition
open InfoGeometry.Thermodynamics.ProjectiveTemperature

/-! ## 1. Generic arithmetic divergence readouts -/

/-- A finite arithmetic divergence readout in projective temperature. -/
/- A divergence readout is already the function it evaluates. The former
one-field structure added no data or law beyond this function. -/
abbrev ArithmeticDivergenceReadout :=
  CountProfile → CountProfile → Finset ℕ → ℝ → ℝ

namespace ArithmeticDivergenceReadout

variable (D : ArithmeticDivergenceReadout)

/-- Pull a divergence readout through a temperature map. -/
def transportTemperature
    (φ : ℝ → ℝ) : ArithmeticDivergenceReadout :=
  fun counts₁ counts₂ support u => D counts₁ counts₂ support (φ u)

@[simp]
theorem transportTemperature_apply
    (φ : ℝ → ℝ)
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) :
    D.transportTemperature φ counts₁ counts₂ support u =
      D counts₁ counts₂ support (φ u) :=
  rfl

end ArithmeticDivergenceReadout

/-! ## 2. Gauge invariance and covariance witnesses -/

/--
Witness that a divergence readout is invariant under global Weyl rescaling of
both arithmetic profiles.
-/
structure GaugeInvariantDivergence
    (D : ArithmeticDivergenceReadout) where
  /-- Simultaneous nonzero scale changes do not change the readout. -/
  invariant_under_scale :
    ∀ (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u c : ℝ),
      c ≠ 0 →
        D (fun n => c * counts₁ n) (fun n => c * counts₂ n) support u =
          D counts₁ counts₂ support u

namespace GaugeInvariantDivergence

variable {D : ArithmeticDivergenceReadout}
variable (G : GaugeInvariantDivergence D)

/-- Re-export simultaneous Weyl-scale invariance. -/
theorem readout_scale_invariant
    (G : GaugeInvariantDivergence D)
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u c : ℝ)
    (hc : c ≠ 0) :
    D (fun n => c * counts₁ n) (fun n => c * counts₂ n) support u =
      D counts₁ counts₂ support u :=
  GaugeInvariantDivergence.invariant_under_scale G counts₁ counts₂ support u c hc

end GaugeInvariantDivergence

/--
Witness that a divergence readout transforms covariantly by a Weyl factor under
a projective temperature transport.
-/
structure GaugeCovariantTemperatureDivergence
    (D : ArithmeticDivergenceReadout)
    (φ : ℝ → ℝ) where
  /-- Weyl factor for the transported temperature coordinate. -/
  weylFactor : ℝ → ℝ

  /-- Covariance law under the temperature transport. -/
  transported_eq_factor_mul :
    ∀ (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ),
      D counts₁ counts₂ support (φ u) =
        weylFactor u * D counts₁ counts₂ support u

namespace GaugeCovariantTemperatureDivergence

variable {D : ArithmeticDivergenceReadout} {φ : ℝ → ℝ}
variable (G : GaugeCovariantTemperatureDivergence D φ)

/-- Re-export temperature covariance. -/
theorem readout_transport_eq_factor_mul
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) :
    D counts₁ counts₂ support (φ u) =
      G.weylFactor u * D counts₁ counts₂ support u :=
  G.transported_eq_factor_mul counts₁ counts₂ support u

end GaugeCovariantTemperatureDivergence

/-! ## 3. Projective inversion specialization -/

/--
Witness that a divergence readout is invariant under projective temperature
inversion `u ↦ u⁻¹`.
-/
structure InversionInvariantDivergence
    (D : ArithmeticDivergenceReadout) where
  /-- Projective inversion invariance. -/
  inversion_invariant :
    ∀ (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ),
      D counts₁ counts₂ support (betaInvert u) =
        D counts₁ counts₂ support u

namespace InversionInvariantDivergence

variable {D : ArithmeticDivergenceReadout}
variable (G : InversionInvariantDivergence D)

/-- Re-export projective inversion invariance. -/
theorem readout_betaInvert_eq
    (G : InversionInvariantDivergence D)
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) :
    D counts₁ counts₂ support (betaInvert u) =
      D counts₁ counts₂ support u :=
  InversionInvariantDivergence.inversion_invariant G counts₁ counts₂ support u

/-- Applying inversion twice returns the original readout. -/
theorem readout_betaInvert_betaInvert_eq
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) :
    D counts₁ counts₂ support (betaInvert (betaInvert u)) =
      D counts₁ counts₂ support u := by
  rw [betaInvert_involutive]

end InversionInvariantDivergence

/-! ## 4. Canonical readouts from existing projective Weyl/prime lanes -/

/-- Arithmetic divergence readout induced by a supplied Weyl-gauge calibration. -/
def readoutOfProjectiveWeylGaugeCalibration
    {State : Type*}
    (C : ProjectiveWeylGaugeCalibration State) :
    ArithmeticDivergenceReadout :=
  fun counts₁ counts₂ support u =>
    C.totalReadout (C.stateOfProfiles counts₁ counts₂ support) u

/-- Prime modular-flow divergence readout induced by a supplied prime calibration. -/
def readoutOfProjectivePrimeCalibration
    {State : Type*}
    (C : ProjectivePrimeCalibration State) :
    Finset ℕ → ℝ → ℝ :=
  fun A u => C.modularFlowReadout (C.stateOfFinset A) u

/-- The Weyl-gauge calibrated divergence factors through scale and shape. -/
theorem readoutOfProjectiveWeylGaugeCalibration_factorization
    {State : Type*}
    (C : ProjectiveWeylGaugeCalibration State)
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) :
    readoutOfProjectiveWeylGaugeCalibration C counts₁ counts₂ support u =
      C.weylScaleReadout (C.stateOfProfiles counts₁ counts₂ support) u *
        C.shapeCoreReadout (C.stateOfProfiles counts₁ counts₂ support) u :=
  C.total_eq_scale_mul_shape counts₁ counts₂ support u

/-- The prime calibration readout agrees with the projective prime partition. -/
theorem readoutOfProjectivePrimeCalibration_eq
    {State : Type*}
    (C : ProjectivePrimeCalibration State)
    (A : Finset ℕ) {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    readoutOfProjectivePrimeCalibration C A u =
      projectivePrimePartition A u :=
  C.flow_eq_projectivePrimePartition A u hu

/-! ## 5. Itakura-Saito shape core and Weyl thermal mass -/

/--
Pointwise Itakura-Saito divergence.

For spectral densities `x` and `y`, this is `x / y - log (x / y) - 1`.
No nonnegativity theorem is asserted here; the positivity hypotheses and proof
belong to a concrete model witness.
-/
def itakuraSaito (x y : ℝ) : ℝ :=
  x / y - Real.log (x / y) - 1

/--
Arithmetic scale-invariant shape divergence between two finite count profiles.

The readout is evaluated on `arithmeticBaseShape`, so the total mass is divided
out before the Itakura-Saito core is read.
-/
def arithmeticShapeDivergence
    (A : Finset ℕ) (countsP countsQ : ℕ → ℝ) : ℝ :=
  Finset.sum A (fun n =>
    itakuraSaito (arithmeticBaseShape A countsP n)
      (arithmeticBaseShape A countsQ n))

/--
Relative thermal mass / Weyl conformal factor between two arithmetic profiles.
-/
def weylThermalScale
    (A : Finset ℕ) (countsP countsQ : ℕ → ℝ) : ℝ :=
  arithmeticTotalMass A countsP / arithmeticTotalMass A countsQ

/-! ## 6. Finite Weyl gauge decomposition witness -/

/--
A calibration witness asserting that a model's total divergence readout
factorizes into a Weyl thermal scale and a scale-invariant Itakura-Saito shape
core.

This is a sidecar contract: it does not prove that every arithmetic or zeta
divergence admits such a factorization.
-/
structure WeylGaugeDecompositionWitness
    (State : Type*) where
  /-- Encode a finite arithmetic support as a geometric state. -/
  stateOfFinset : Finset ℕ → State

  /-- Model-specific total divergence readout. -/
  totalDivergence : State → State → ℝ

  /-- Supplied Weyl gauge decomposition law. -/
  weyl_decomposition_law :
    ∀ (A : Finset ℕ) (countsP countsQ : ℕ → ℝ),
      0 < arithmeticTotalMass A countsP →
      0 < arithmeticTotalMass A countsQ →
        totalDivergence (stateOfFinset A) (stateOfFinset A) =
          weylThermalScale A countsP countsQ *
            arithmeticShapeDivergence A countsP countsQ

namespace WeylGaugeDecompositionWitness

variable {State : Type*}
variable (W : WeylGaugeDecompositionWitness State)

/--
If the thermal masses are identical, the Weyl scale is `1`, so the total
divergence reduces to the scale-invariant Itakura-Saito shape core.
-/
theorem totalDivergence_eq_shape_of_equal_mass
    (A : Finset ℕ) (countsP countsQ : ℕ → ℝ)
    (hP : 0 < arithmeticTotalMass A countsP)
    (hQ : 0 < arithmeticTotalMass A countsQ)
    (hMassEq : arithmeticTotalMass A countsP = arithmeticTotalMass A countsQ) :
    W.totalDivergence (W.stateOfFinset A) (W.stateOfFinset A) =
      arithmeticShapeDivergence A countsP countsQ := by
  have hScaleOne : weylThermalScale A countsP countsQ = 1 := by
    unfold weylThermalScale
    rw [hMassEq]
    exact div_self hQ.ne'
  rw [W.weyl_decomposition_law A countsP countsQ hP hQ]
  rw [hScaleOne]
  ring

end WeylGaugeDecompositionWitness

end InfoGeometry.Arithmetic.WeylArithmeticDivergence
