import InfoGeometry.Canonical.DensityWeightIntertwinerBridge
import Mathlib.Tactic.Abel

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.WeightedWeylNormalizationBridge

Thin bridge making the weighted Weyl / projective renormalization picture
explicit on the doubled carrier.

The key repo-native point is:

- the density-weight lift is a generator-side correction `w • K`,
- the induced weighted dynamics therefore acquires an explicit commutator
  correction `w • [K, A]`,
- the weighted Weyl correction stays entirely on the operatorial
  generator/dynamics/readout side.

This keeps the bridge typesafe: scalar/projective anchor cocycles are handled
elsewhere and are not mixed into the weighted transport surface here.
-/

namespace InfoGeometry.Canonical.WeightedWeylNormalizationBridge

open InfoGeometry.Canonical.DensityWeightIntertwinerBridge
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Krein

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- theorem-class: transport lemma
The weighted transport generator is the zero-weight generator plus the explicit
weighted phase-axis correction. -/
@[rep_depth transport]
theorem densityWeightLiftedTransportGenerator_eq_zeroWeight_add_weighted_phaseAxis
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (w : ℝ) :
    InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedTransportGenerator P ψ w
      =
    InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedTransportGenerator P ψ 0
      + w • InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E) := by
  change
    InfoGeometry.Canonical.ThermodynamicGenerator.souriauTemperatureVector (E := E) P ψ
      + w • InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)
      =
    InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedTransportGenerator P ψ 0
      + w • InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)
  rw [InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedTransportGenerator_zero
    (E := E) (P := P) (ψ := ψ)]

/-- theorem-class: transport lemma
The weighted dynamics is the zero-weight dynamics plus the explicit weighted
phase-axis commutator correction. -/
@[rep_depth transport]
theorem densityWeightLiftedDynamics_eq_zeroWeight_add_weighted_phaseAxis_commutator
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH) (w : ℝ) :
    InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedDynamics P ψ A w
      =
    InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedDynamics P ψ A 0
      +
    w • transportCommutator (E := E)
      (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)) A := by
  change
    transportCommutator (E := E)
      (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedTransportGenerator P ψ w) A
      =
    InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedDynamics P ψ A 0
      + w • transportCommutator (E := E)
          (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)) A
  rw [densityWeightLiftedTransportGenerator_eq_zeroWeight_add_weighted_phaseAxis
    (P := P) (ψ := ψ) (w := w)]
  rw [InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedDynamics_zero
    (E := E) (P := P) (ψ := ψ) (A := A)]
  apply ContinuousLinearMap.ext
  intro x
  apply DoubledSpace.ext <;>
    simp [transportCommutator, sub_eq_add_neg, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.smul_comp]
  · abel
  · abel

/-- theorem-class: coherence theorem
The weighted doubled-space metric/phase readout is the zero-weight readout plus
the explicit weighted phase-axis response. -/
@[rep_depth transport]
theorem densityWeightLiftedReadout_pair_eq_zeroWeight_add_weighted_phaseAxisReadout
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH) (w : ℝ) :
    ( (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout P ψ A w).metric
    , (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout P ψ A w).phase )
      =
    ( (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout P ψ A 0).metric
        + w • InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
            (E := E) (transportCommutator (E := E)
              (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)) A)
    , (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout P ψ A 0).phase
        + w • InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
            (E := E) (transportCommutator (E := E)
              (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)) A) ) := by
  apply Prod.ext
  · ext u v
    have hDyn :=
      densityWeightLiftedDynamics_eq_zeroWeight_add_weighted_phaseAxis_commutator
        (P := P) (ψ := ψ) (A := A) (w := w)
    simp [InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout, hDyn,
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_add,
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_smul]
  · ext u v
    have hDyn :=
      densityWeightLiftedDynamics_eq_zeroWeight_add_weighted_phaseAxis_commutator
        (P := P) (ψ := ψ) (A := A) (w := w)
    simp [InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout, hDyn,
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator_add,
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator_smul]

end Core

end InfoGeometry.Canonical.WeightedWeylNormalizationBridge
