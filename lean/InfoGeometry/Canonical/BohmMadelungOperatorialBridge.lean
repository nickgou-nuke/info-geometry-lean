import InfoGeometry.Canonical.PolarizedMadelungBridge
import InfoGeometry.Canonical.ThermodynamicGenerator
import InfoGeometry.Canonical.SouriauPlanckVector

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.BohmMadelungOperatorialBridge

Thin theorem surface exposing the repo-native Bohm-Madelung decomposition on the
doubled real Krein carrier.

This file introduces no scalar wavefunction shell and no second ontology. It
only packages the already-owned equalities showing that:

- phase is the orbit/readout induced by the internal axis `K = Jε`,
- the operatorial state evolution splits into gauge and source branches,
- and for a state-independent generator seed, the `K`-response is carried by the
  source branch while the gauge branch is `K`-silent.
-/

namespace InfoGeometry.Canonical.BohmMadelungOperatorialBridge

open InfoGeometry.Canonical.PolarizedMadelungBridge
open InfoGeometry.Canonical.StateDependentTransport
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.ThermodynamicGenerator

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "Kop" => InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E)

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

@[rep_depth krein]
theorem polarizedDoubledAmplitude_phaseOrbit_eq_dilationOrbit
    (S : PolarizedDoubledAmplitude (E := E)) (θ : ℝ) :
    S.phaseOrbit θ = (NormedSpace.exp (θ • InfoGeometry.Krein.dilationOperator (E := E))) S.ψ :=
  PolarizedDoubledAmplitude.phaseOrbit_eq_dilationOrbit (E := E) S θ

@[rep_depth krein]
theorem polarizedDoubledAmplitude_modularConjugationJ_phaseOrbit_eq_reverse
    (S : PolarizedDoubledAmplitude (E := E)) (θ : ℝ) :
    InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E) (S.phaseOrbit θ)
      = (NormedSpace.exp ((-θ) • Kop))
          ((InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E)) S.ψ) :=
  PolarizedDoubledAmplitude.modularConjugationJ_phaseOrbit_eq_reverse (E := E) S θ

@[rep_depth transport]
theorem stateGeneratorField_phaseReadout_eq_metric_comp_complex_i
    (G : StateGeneratorField (E := E)) (ψ : H₂) (A : EndH) :
    StateGeneratorField.statePhaseReadout (E := E) G ψ A
      =
    (StateGeneratorField.stateMetricReadout (E := E) G ψ A).compLeft
      (InfoGeometry.Krein.complex_i (E := E)) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i] using
    (StateGeneratorField.statePhaseReadout_eq_metric_comp_K (E := E) G ψ A)

@[rep_depth transport]
theorem stateGeneratorField_phaseReadout_eq_metric_comp_K
    (G : StateGeneratorField (E := E)) (ψ : H₂) (A : EndH) :
    StateGeneratorField.statePhaseReadout (E := E) G ψ A
      =
    (StateGeneratorField.stateMetricReadout (E := E) G ψ A).compLeft
      (InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E)) := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i] using
    (stateGeneratorField_phaseReadout_eq_metric_comp_complex_i (E := E) G ψ A)

@[rep_depth transport]
theorem stateGeneratorField_inducedDerivation_eq_gauge_add_source
    (G : StateGeneratorField (E := E)) (ψ : H₂) (A : EndH) :
    StateGeneratorField.stateInducedDerivation (E := E) G ψ A
      =
    StateGeneratorField.stateGaugeDerivation (E := E) G ψ A
      +
    StateGeneratorField.stateSourceDerivation (E := E) G ψ A :=
  StateGeneratorField.stateInducedDerivation_eq_gauge_add_source (E := E) G ψ A

/-- Constant state-generator field attached to a single doubled-space seed. -/
abbrev constantStateGeneratorField (H : EndH) : StateGeneratorField (E := E) :=
  StateGeneratorField.mk (generator := fun _ => H)

omit [CompleteSpace E] in
@[simp] theorem constantStateGeneratorField_generator_apply
    (H : EndH) (ψ : H₂) :
    (constantStateGeneratorField (E := E) H).generator ψ = H := rfl

@[rep_depth transport, simp]
theorem constantStateGeneratorField_relativeModularGenerator_eq_modularTransportGenerator
    (H : EndH) (ψ : H₂) :
    stateRelativeModularGenerator (E := E)
        (StateGeneratorField.toStateModularDatum (E := E)
          (constantStateGeneratorField (E := E) H))
        ψ
      =
    modularTransportGenerator (E := E) H := by
  rfl

@[rep_depth transport, simp]
theorem constantStateGeneratorField_stateInducedDerivation_eq_relativeModularDeriv
    (H A : EndH) (ψ : H₂) :
    StateGeneratorField.stateInducedDerivation (E := E)
        (constantStateGeneratorField (E := E) H) ψ A
      =
    relativeModularDeriv (E := E) H A := by
  rfl

@[rep_depth transport, simp]
theorem constantStateGeneratorField_stateGaugeGenerator_eq_phaseLinearPart
    (H : EndH) (ψ : H₂) :
    stateGaugeGenerator (E := E)
        (StateGeneratorField.toStateModularDatum (E := E)
          (constantStateGeneratorField (E := E) H))
        ψ
      =
    phaseLinearPart (E := E) (modularTransportGenerator (E := E) H) := by
  rfl

@[rep_depth transport, simp]
theorem constantStateGeneratorField_stateSourceGenerator_eq_phaseAntilinearPart
    (H : EndH) (ψ : H₂) :
    stateSourceGenerator (E := E)
        (StateGeneratorField.toStateModularDatum (E := E)
          (constantStateGeneratorField (E := E) H))
        ψ
      =
    phaseAntilinearPart (E := E) (modularTransportGenerator (E := E) H) := by
  rfl

@[rep_depth transport, simp]
theorem constantStateGeneratorField_stateGaugeDerivation_eq_transportCommutator_phaseLinearPart
    (H A : EndH) (ψ : H₂) :
    StateGeneratorField.stateGaugeDerivation (E := E)
        (constantStateGeneratorField (E := E) H) ψ A
      =
    transportCommutator (E := E)
      (phaseLinearPart (E := E) (modularTransportGenerator (E := E) H)) A := by
  rfl

@[rep_depth transport, simp]
theorem constantStateGeneratorField_stateSourceDerivation_eq_transportCommutator_phaseAntilinearPart
    (H A : EndH) (ψ : H₂) :
    StateGeneratorField.stateSourceDerivation (E := E)
        (constantStateGeneratorField (E := E) H) ψ A
      =
    transportCommutator (E := E)
      (phaseAntilinearPart (E := E) (modularTransportGenerator (E := E) H)) A := by
  rfl

@[rep_depth transport]
theorem constantStateGeneratorField_stateInducedDerivation_eq_phaseLinear_add_phaseAntilinear_transport
    (H A : EndH) (ψ : H₂) :
    StateGeneratorField.stateInducedDerivation (E := E)
        (constantStateGeneratorField (E := E) H) ψ A
      =
    transportCommutator (E := E)
      (phaseLinearPart (E := E) (modularTransportGenerator (E := E) H)) A
      +
    transportCommutator (E := E)
      (phaseAntilinearPart (E := E) (modularTransportGenerator (E := E) H)) A := by
  rw [stateGeneratorField_inducedDerivation_eq_gauge_add_source]
  rw [constantStateGeneratorField_stateGaugeDerivation_eq_transportCommutator_phaseLinearPart]
  rw [constantStateGeneratorField_stateSourceDerivation_eq_transportCommutator_phaseAntilinearPart]

@[rep_depth transport, simp]
theorem constantStateGeneratorField_stateQGTReadout_apply_eq_metricPhase_relativeModularDeriv
    (H A : EndH) (ψ u v : H₂) :
    ( (StateGeneratorField.stateQGTReadout (E := E)
          (constantStateGeneratorField (E := E) H) ψ A).metric u v
    , (StateGeneratorField.stateQGTReadout (E := E)
          (constantStateGeneratorField (E := E) H) ψ A).phase u v )
      =
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E) (relativeModularDeriv (E := E) H A) u v
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E) (relativeModularDeriv (E := E) H A) u v ) := by
  rfl

@[rep_depth transport]
theorem constantStateGeneratorField_stateQGTReadout_pair_eq_phaseLinearAntilinear_transport_pair
    (H A : EndH) (ψ : H₂) :
    ( (StateGeneratorField.stateQGTReadout (E := E)
          (constantStateGeneratorField (E := E) H) ψ A).metric
    , (StateGeneratorField.stateQGTReadout (E := E)
          (constantStateGeneratorField (E := E) H) ψ A).phase )
      =
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E) (modularTransportGenerator (E := E) H)) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E) (modularTransportGenerator (E := E) H)) A)
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E) (modularTransportGenerator (E := E) H)) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E) (modularTransportGenerator (E := E) H)) A) ) := by
  apply Prod.ext
  · ext u v
    have hFst :
        ((StateGeneratorField.stateQGTReadout (E := E)
            (constantStateGeneratorField (E := E) H) ψ A).metric u v)
          =
        InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
          (E := E) (relativeModularDeriv (E := E) H A) u v := by
      simpa using
        congrArg Prod.fst
          (constantStateGeneratorField_stateQGTReadout_apply_eq_metricPhase_relativeModularDeriv
            (E := E) H A ψ u v)
    rw [hFst]
    rw [← constantStateGeneratorField_stateInducedDerivation_eq_relativeModularDeriv
      (E := E) (H := H) (A := A) (ψ := ψ)]
    rw [stateGeneratorField_inducedDerivation_eq_gauge_add_source
      (E := E) (G := constantStateGeneratorField (E := E) H) (ψ := ψ) (A := A)]
    rw [InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_add]
    rw [constantStateGeneratorField_stateGaugeDerivation_eq_transportCommutator_phaseLinearPart
      (E := E) (H := H) (A := A) (ψ := ψ)]
    rw [constantStateGeneratorField_stateSourceDerivation_eq_transportCommutator_phaseAntilinearPart
      (E := E) (H := H) (A := A) (ψ := ψ)]
  · ext u v
    have hSnd :
        ((StateGeneratorField.stateQGTReadout (E := E)
            (constantStateGeneratorField (E := E) H) ψ A).phase u v)
          =
        InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
          (E := E) (relativeModularDeriv (E := E) H A) u v := by
      simpa using
        congrArg Prod.snd
          (constantStateGeneratorField_stateQGTReadout_apply_eq_metricPhase_relativeModularDeriv
            (E := E) H A ψ u v)
    rw [hSnd]
    rw [← constantStateGeneratorField_stateInducedDerivation_eq_relativeModularDeriv
      (E := E) (H := H) (A := A) (ψ := ψ)]
    rw [stateGeneratorField_inducedDerivation_eq_gauge_add_source
      (E := E) (G := constantStateGeneratorField (E := E) H) (ψ := ψ) (A := A)]
    rw [InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator_add]
    rw [constantStateGeneratorField_stateGaugeDerivation_eq_transportCommutator_phaseLinearPart
      (E := E) (H := H) (A := A) (ψ := ψ)]
    rw [constantStateGeneratorField_stateSourceDerivation_eq_transportCommutator_phaseAntilinearPart
      (E := E) (H := H) (A := A) (ψ := ψ)]

@[rep_depth transport]
theorem potentialDatum_constantStateGeneratorField_stateQGTReadout_pair_eq_comparisonReadout_pair
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    ( (StateGeneratorField.stateQGTReadout (E := E)
          (constantStateGeneratorField (E := E) (P.modularData.modularSeed ψ))
          ψ A).metric
    , (StateGeneratorField.stateQGTReadout (E := E)
          (constantStateGeneratorField (E := E) (P.modularData.modularSeed ψ))
          ψ A).phase )
      =
    ( comparisonMetricReadout (E := E) P ψ A
    , comparisonPhaseReadout (E := E) P ψ A ) := by
  rfl

@[rep_depth transport]
theorem potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_iff_isPotentialKillingOperator
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    ( (StateGeneratorField.stateQGTReadout (E := E)
          (constantStateGeneratorField (E := E) (P.modularData.modularSeed ψ))
          ψ A).metric
    , (StateGeneratorField.stateQGTReadout (E := E)
          (constantStateGeneratorField (E := E) (P.modularData.modularSeed ψ))
          ψ A).phase )
      =
    (0, 0)
      ↔
    IsPotentialKillingOperator (E := E) P ψ A := by
  rw [potentialDatum_constantStateGeneratorField_stateQGTReadout_pair_eq_comparisonReadout_pair]
  simpa [IsThermodynamicReadoutStationary] using
    (isPotentialKillingOperator_iff_isThermodynamicReadoutStationary
      (E := E) P ψ A).symm

@[rep_depth transport]
theorem potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_of_equilibriumSeed
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hEq : InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed (E := E) P ψ A) :
    ( (StateGeneratorField.stateQGTReadout (E := E)
          (constantStateGeneratorField (E := E) (P.modularData.modularSeed ψ))
          ψ A).metric
    , (StateGeneratorField.stateQGTReadout (E := E)
          (constantStateGeneratorField (E := E) (P.modularData.modularSeed ψ))
          ψ A).phase )
      =
    (0, 0) := by
  have hStationary :
      IsThermodynamicReadoutStationary (E := E) P ψ A :=
    InfoGeometry.Canonical.SouriauPlanckVector.isThermodynamicReadoutStationary_of_equilibriumSeed
      (E := E) hEq
  rw [potentialDatum_constantStateGeneratorField_stateQGTReadout_pair_eq_comparisonReadout_pair]
  simpa [IsThermodynamicReadoutStationary] using hStationary

@[rep_depth transport]
theorem potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_of_firstVariation_eq_zero_of_probeFaithful
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hFaithful : ProbeFaithful (E := E) P)
    (hFirst : firstVariation (E := E) P ψ A = 0) :
    ( (StateGeneratorField.stateQGTReadout (E := E)
          (constantStateGeneratorField (E := E) (P.modularData.modularSeed ψ))
          ψ A).metric
    , (StateGeneratorField.stateQGTReadout (E := E)
          (constantStateGeneratorField (E := E) (P.modularData.modularSeed ψ))
          ψ A).phase )
      =
    (0, 0) := by
  rw [potentialDatum_constantStateGeneratorField_stateQGTReadout_pair_eq_comparisonReadout_pair]
  exact comparisonReadout_pair_eq_zero_of_firstVariation_eq_zero_of_probeFaithful
    (E := E) P ψ A hFaithful hFirst

@[rep_depth transport]
theorem potentialDatum_constantStateGeneratorField_kSplitReadout_stationary_iff_isPotentialKillingOperator
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (modularTransportGenerator (E := E) (P.modularData.modularSeed ψ))) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (modularTransportGenerator (E := E) (P.modularData.modularSeed ψ))) A)
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (modularTransportGenerator (E := E) (P.modularData.modularSeed ψ))) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (modularTransportGenerator (E := E) (P.modularData.modularSeed ψ))) A) )
      =
    (0, 0)
      ↔
    IsPotentialKillingOperator (E := E) P ψ A := by
  rw [← constantStateGeneratorField_stateQGTReadout_pair_eq_phaseLinearAntilinear_transport_pair
    (E := E) (H := P.modularData.modularSeed ψ) (A := A) (ψ := ψ)]
  exact
    potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_iff_isPotentialKillingOperator
      (E := E) P ψ A

@[rep_depth transport]
theorem potentialDatum_constantStateGeneratorField_kSplitReadout_stationary_of_equilibriumSeed
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hEq : InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed (E := E) P ψ A) :
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (modularTransportGenerator (E := E) (P.modularData.modularSeed ψ))) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (modularTransportGenerator (E := E) (P.modularData.modularSeed ψ))) A)
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (modularTransportGenerator (E := E) (P.modularData.modularSeed ψ))) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (modularTransportGenerator (E := E) (P.modularData.modularSeed ψ))) A) )
      =
    (0, 0) := by
  rw [← constantStateGeneratorField_stateQGTReadout_pair_eq_phaseLinearAntilinear_transport_pair
    (E := E) (H := P.modularData.modularSeed ψ) (A := A) (ψ := ψ)]
  exact
    potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_of_equilibriumSeed
      (E := E) P ψ A hEq

@[rep_depth transport]
theorem potentialDatum_constantStateGeneratorField_kSplitReadout_stationary_of_firstVariation_eq_zero_of_probeFaithful
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH)
    (hFaithful : ProbeFaithful (E := E) P)
    (hFirst : firstVariation (E := E) P ψ A = 0) :
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (modularTransportGenerator (E := E) (P.modularData.modularSeed ψ))) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (modularTransportGenerator (E := E) (P.modularData.modularSeed ψ))) A)
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (modularTransportGenerator (E := E) (P.modularData.modularSeed ψ))) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (modularTransportGenerator (E := E) (P.modularData.modularSeed ψ))) A) )
      =
    (0, 0) := by
  rw [← constantStateGeneratorField_stateQGTReadout_pair_eq_phaseLinearAntilinear_transport_pair
    (E := E) (H := P.modularData.modularSeed ψ) (A := A) (ψ := ψ)]
  exact
    potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_of_firstVariation_eq_zero_of_probeFaithful
      (E := E) P ψ A hFaithful hFirst

@[rep_depth transport]
theorem constantStateGeneratorField_stateGaugeGenerator_isPhaseLinear
    (H : EndH) (ψ : H₂) :
    IsPhaseLinear (E := E)
      (stateGaugeGenerator (E := E)
        (StateGeneratorField.toStateModularDatum (E := E)
          (constantStateGeneratorField (E := E) H))
        ψ) := by
  rw [constantStateGeneratorField_stateGaugeGenerator_eq_phaseLinearPart]
  exact phaseLinearPart_isPhaseLinear (E := E) (modularTransportGenerator (E := E) H)

@[rep_depth transport]
theorem constantStateGeneratorField_stateSourceGenerator_isPhaseAntilinear
    (H : EndH) (ψ : H₂) :
    IsPhaseAntilinear (E := E)
      (stateSourceGenerator (E := E)
        (StateGeneratorField.toStateModularDatum (E := E)
          (constantStateGeneratorField (E := E) H))
        ψ) := by
  rw [constantStateGeneratorField_stateSourceGenerator_eq_phaseAntilinearPart]
  exact phaseAntilinearPart_isPhaseAntilinear (E := E) (modularTransportGenerator (E := E) H)

@[rep_depth transport]
theorem constantStateGeneratorField_phaseAxisResponse_stateGaugeGenerator_eq_zero
    (H : EndH) (ψ : H₂) :
    phaseAxisResponse (E := E)
      (stateGaugeGenerator (E := E)
        (StateGeneratorField.toStateModularDatum (E := E)
          (constantStateGeneratorField (E := E) H))
        ψ)
      = 0 := by
  apply phaseAxisResponse_linear_vanishing
  exact constantStateGeneratorField_stateGaugeGenerator_isPhaseLinear (E := E) H ψ

@[rep_depth transport]
theorem constantStateGeneratorField_phaseAxisResponse_stateSourceGenerator_eq_two_smul_comp_K
    (H : EndH) (ψ : H₂) :
    phaseAxisResponse (E := E)
      (stateSourceGenerator (E := E)
        (StateGeneratorField.toStateModularDatum (E := E)
          (constantStateGeneratorField (E := E) H))
        ψ)
      =
    (2 : ℝ) •
      ((stateSourceGenerator (E := E)
          (StateGeneratorField.toStateModularDatum (E := E)
            (constantStateGeneratorField (E := E) H))
          ψ).comp Kop) := by
  apply phaseAxisResponse_antilinear_source
  exact constantStateGeneratorField_stateSourceGenerator_isPhaseAntilinear (E := E) H ψ

@[rep_depth transport]
theorem constantStateGeneratorField_phaseAxisForce_eq_from_stateSourceGenerator
    (H : EndH) (ψ : H₂) :
    phaseAxisForce (E := E)
      (stateRelativeModularGenerator (E := E)
        (StateGeneratorField.toStateModularDatum (E := E)
          (constantStateGeneratorField (E := E) H))
        ψ)
      =
    (2 : ℝ) •
      ((stateSourceGenerator (E := E)
          (StateGeneratorField.toStateModularDatum (E := E)
            (constantStateGeneratorField (E := E) H))
          ψ).comp Kop) := by
  rw [constantStateGeneratorField_relativeModularGenerator_eq_modularTransportGenerator]
  rw [constantStateGeneratorField_stateSourceGenerator_eq_phaseAntilinearPart]
  exact phaseAxisForce_eq_from_phaseAntilinearPart
    (E := E) (modularTransportGenerator (E := E) H)

end Core

end InfoGeometry.Canonical.BohmMadelungOperatorialBridge
