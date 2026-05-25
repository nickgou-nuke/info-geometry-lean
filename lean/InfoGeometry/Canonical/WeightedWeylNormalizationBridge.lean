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

/--
Coordinate-free Weyl/Lie derivation packet on the real doubled carrier.

This is the repo-native replacement for coordinate partial derivatives:

* the algebraic derivation is the commutator `ad_X(A) = [X,A]`;
* the Weyl-modified derivation uses the density-weight lifted generator
  `β + w • D`;
* the modified derivation splits into the zero-weight Lie derivation plus the
  explicit scale-axis commutator correction.

No finite carrier, coordinate chart, trace, or scalar central-charge shortcut is
introduced.
-/
@[rep_depth transport]
theorem coordinateFreeWeylLieDerivation_packet
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH) (w : ℝ) :
    InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedTransportGenerator
        P ψ w =
      InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedTransportGenerator
        P ψ 0
        + w • InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis
          (E := E)
      ∧
    InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedDynamics
        P ψ A w =
      transportCommutator (E := E)
        (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedTransportGenerator
          P ψ w) A
      ∧
    InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedDynamics
        P ψ A 0 =
      transportCommutator (E := E)
        (InfoGeometry.Canonical.ThermodynamicGenerator.souriauTemperatureVector
          (E := E) P ψ) A
      ∧
    InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedDynamics
        P ψ A w =
      InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedDynamics
        P ψ A 0
        + w • transportCommutator (E := E)
          (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis
            (E := E)) A := by
  exact
    ⟨densityWeightLiftedTransportGenerator_eq_zeroWeight_add_weighted_phaseAxis
        (P := P) (ψ := ψ) (w := w),
      rfl,
      InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedDynamics_zero
        (E := E) (P := P) (ψ := ψ) (A := A),
      densityWeightLiftedDynamics_eq_zeroWeight_add_weighted_phaseAxis_commutator
        (P := P) (ψ := ψ) (A := A) (w := w)⟩

attribute [terminal] coordinateFreeWeylLieDerivation_packet

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

/--
At equilibrium, the weighted density-lifted readout is exactly the explicit
weighted phase-axis response.

This is still an infinite operatorial theorem on the doubled carrier. The
zero-weight packet is killed by the theorem-backed Gibbs-Souriau equilibrium
seed, leaving only the weight-sector correction.
-/
@[rep_depth transport]
theorem densityWeightLiftedReadout_pair_eq_weighted_phaseAxisReadout_of_equilibriumSeed
    {P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)}
    {ψ : H₂} {A : EndH}
    (hEq : InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed (E := E) P ψ A)
    (w : ℝ) :
    ((InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout (E := E) P ψ A w).metric,
      (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout (E := E) P ψ A w).phase)
      =
    (w • InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
          (E := E)
          (transportCommutator (E := E)
            (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)) A),
      w • InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
          (E := E)
          (transportCommutator (E := E)
            (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)) A)) := by
  have hSplit :=
    densityWeightLiftedReadout_pair_eq_zeroWeight_add_weighted_phaseAxisReadout
      (P := P) (ψ := ψ) (A := A) (w := w)
  have hZero :=
    InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout_zero_pair_eq_zero_of_equilibriumSeed
      (E := E) hEq
  have hMetricZero :
      (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout (E := E) P ψ A 0).metric = 0 := by
    exact congrArg Prod.fst hZero
  have hPhaseZero :
      (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout (E := E) P ψ A 0).phase = 0 := by
    exact congrArg Prod.snd hZero
  simpa [hMetricZero, hPhaseZero] using hSplit

/--
Faithful probing plus vanishing first variation kill the zero-weight packet, so
only the explicit weighted phase-axis response remains.
-/
@[rep_depth transport]
theorem densityWeightLiftedReadout_pair_eq_weighted_phaseAxisReadout_of_firstVariation_eq_zero_of_probeFaithful
    {P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)}
    {ψ : H₂} {A : EndH}
    (hFaithful : InfoGeometry.Canonical.ThermodynamicGenerator.ProbeFaithful (E := E) P)
    (hFirst : InfoGeometry.Canonical.RelativeModularPotential.firstVariation (E := E) P ψ A = 0)
    (w : ℝ) :
    ((InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout (E := E) P ψ A w).metric,
      (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout (E := E) P ψ A w).phase)
      =
    (w • InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
          (E := E)
          (transportCommutator (E := E)
            (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)) A),
      w • InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
          (E := E)
          (transportCommutator (E := E)
            (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)) A)) := by
  have hSplit :=
    densityWeightLiftedReadout_pair_eq_zeroWeight_add_weighted_phaseAxisReadout
      (P := P) (ψ := ψ) (A := A) (w := w)
  have hZero :=
    densityWeightLiftedReadout_zero_pair_eq_zero_of_firstVariation_eq_zero_of_probeFaithful
      (E := E) (P := P) (ψ := ψ) (A := A) hFaithful hFirst
  have hMetricZero :
      (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout (E := E) P ψ A 0).metric = 0 := by
    exact congrArg Prod.fst hZero
  have hPhaseZero :
      (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout (E := E) P ψ A 0).phase = 0 := by
    exact congrArg Prod.snd hZero
  simpa [hMetricZero, hPhaseZero] using hSplit

/--
If the observable channel commutes with the density-weight phase axis, then a
Gibbs-Souriau equilibrium seed kills the full weighted density-lifted readout at
any weight.

This is an infinite operatorial closure theorem on the doubled carrier. It does
not use any finite response matrix: equilibrium kills the zero-weight packet,
and phase-axis commutation kills the explicit weighted correction.
-/
@[rep_depth transport]
theorem densityWeightLiftedReadout_pair_eq_zero_of_equilibriumSeed_of_commute_phaseAxis
    {P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)}
    {ψ : H₂} {A : EndH}
    (hEq : InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed (E := E) P ψ A)
    (hComm :
      Commute A
        (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)))
    (w : ℝ) :
    ((InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout (E := E) P ψ A w).metric,
      (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout (E := E) P ψ A w).phase)
      = (0, 0) := by
  have hWeighted :=
    densityWeightLiftedReadout_pair_eq_weighted_phaseAxisReadout_of_equilibriumSeed
      (E := E) hEq w
  have hCommZero :
      transportCommutator (E := E)
        (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)) A
        = 0 := by
    unfold transportCommutator
    exact sub_eq_zero.mpr hComm.eq.symm
  have hCommZeroComplex :
      transportCommutator (E := E) (InfoGeometry.Krein.complex_i (E := E)) A = 0 := by
    rw [← InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis_eq_complex_i]
    exact hCommZero
  have hMetricZero :
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator (E := E)
        (transportCommutator (E := E)
          (InfoGeometry.Krein.complex_i (E := E)) A) = 0 := by
    rw [hCommZeroComplex]
    ext u v
    simp [InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator]
  have hBerryZero :
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator (E := E)
        (transportCommutator (E := E)
          (InfoGeometry.Krein.complex_i (E := E)) A) = 0 := by
    rw [hCommZeroComplex]
    ext u v
    simp [InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator]
  apply Prod.ext
  · have hMetric := congrArg Prod.fst hWeighted
    simpa [hMetricZero] using hMetric
  · have hPhase := congrArg Prod.snd hWeighted
    simpa [hBerryZero] using hPhase

/--
On the canonical phase-axis observable branch, the phase-axis commutation
hypothesis is discharged constructively by reflexivity.
-/
@[rep_depth transport]
theorem densityWeightLiftedReadout_phaseAxis_pair_eq_zero_of_equilibriumSeed
    {P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E)}
    {ψ : H₂}
    (hEq :
      InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed
        (E := E) P ψ
        (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)))
    (w : ℝ) :
    ((InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout
        (E := E) P ψ
        (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)) w).metric,
      (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout
        (E := E) P ψ
        (InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E)) w).phase)
      = (0, 0) := by
  exact densityWeightLiftedReadout_pair_eq_zero_of_equilibriumSeed_of_commute_phaseAxis
    (E := E) (A := InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis (E := E))
    hEq (Commute.refl _) w

end Core

end InfoGeometry.Canonical.WeightedWeylNormalizationBridge
