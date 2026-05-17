import InfoGeometry.Canonical.RelationalInformationCore
import InfoGeometry.Canonical.StandardFormCore
import InfoGeometry.Canonical.ThermodynamicGenerator
import InfoGeometry.Canonical.SouriauPlanckVector
import InfoGeometry.Projective.Dynamics

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.MajoranaKreinCartanSplit

Bridge file for the red-line lift

`count -> projective rays -> doubled Krein carrier -> transport/readout split`.

This file does not introduce a new Cartan ontology. It only exposes that the
existing doubled-space modular atoms `J`, `ε`, `K = Jε` already descend to the
projective ray layer, and that the comparison-state modular transport spine is
already split by the `K`-phase parity decomposition into its compact/gauge and
noncompact/source sectors.
-/

namespace InfoGeometry.Canonical.MajoranaKreinCartanSplit

open InfoGeometry.Canonical.StandardFormCore
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.StateDependentTransport
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.ThermodynamicGenerator

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-! ## Projective base: descended involution system -/

@[rep_depth projective, simp]
theorem projectiveDynamics_J_eq_projectiveMap_tomitaAtomSeed_J :
    InfoGeometry.ProjectiveDynamics.J (E := E) =
      InfoGeometry.Projective.projectiveMap (E := E) (InfoGeometry.Krein.modular_j (E := E)) := by
  rfl

@[rep_depth projective, simp]
theorem projectiveDynamics_epsilon_eq_projectiveMap_tomitaAtomSeed_eps :
    InfoGeometry.ProjectiveDynamics.epsilon (E := E) =
      InfoGeometry.Projective.projectiveMap (E := E) (InfoGeometry.Krein.spectral_epsilon (E := E)) := by
  rfl

@[rep_depth projective, simp]
theorem projectiveDynamics_I_eq_projectiveMap_tomitaAtomSeed_phaseAxis :
    InfoGeometry.ProjectiveDynamics.I (E := E) =
      InfoGeometry.Projective.projectiveMap (E := E) (InfoGeometry.Krein.complex_i (E := E)) := by
  rfl

@[rep_depth projective]
theorem projectiveDynamics_tomitaAtomSeed_J_comp_eps :
    (InfoGeometry.ProjectiveDynamics.J (E := E))
      ∘ (InfoGeometry.ProjectiveDynamics.epsilon (E := E))
      =
    InfoGeometry.ProjectiveDynamics.I (E := E) := by
  exact InfoGeometry.ProjectiveDynamics.J_comp_epsilon (E := E)

@[rep_depth projective]
theorem projectiveDynamics_tomitaAtomSeed_commute :
    (InfoGeometry.ProjectiveDynamics.J (E := E))
      ∘ (InfoGeometry.ProjectiveDynamics.epsilon (E := E))
      =
    (InfoGeometry.ProjectiveDynamics.epsilon (E := E))
      ∘ (InfoGeometry.ProjectiveDynamics.J (E := E)) := by
  exact InfoGeometry.ProjectiveDynamics.J_epsilon_commute (E := E)

/-! ## Doubled transport: `K`-compact / `K`-noncompact split -/

@[rep_depth transport]
theorem comparisonTransportGenerator_eq_gauge_add_source
    (R : RelationalInformationDatum (E := E)) :
    comparisonTransportGenerator R
      =
    stateGaugeGenerator (E := E) R.modularData R.comparisonState
      +
    stateSourceGenerator (E := E) R.modularData R.comparisonState := by
  simpa [comparisonTransportGenerator, stateRelativeModularGenerator,
    stateGaugeGenerator, stateSourceGenerator] using
    (modularTransportGenerator_split (E := E) (R.modularData.modularSeed R.comparisonState))

@[rep_depth transport, simp]
theorem comparisonGaugeGenerator_eq_phaseLinearPart_comparisonTransportGenerator
    (R : RelationalInformationDatum (E := E)) :
    stateGaugeGenerator (E := E) R.modularData R.comparisonState
      =
    phaseLinearPart (E := E) (comparisonTransportGenerator R) := by
  rfl

@[rep_depth transport, simp]
theorem comparisonSourceGenerator_eq_phaseAntilinearPart_comparisonTransportGenerator
    (R : RelationalInformationDatum (E := E)) :
    stateSourceGenerator (E := E) R.modularData R.comparisonState
      =
    phaseAntilinearPart (E := E) (comparisonTransportGenerator R) := by
  rfl

@[rep_depth transport]
theorem comparisonGaugeGenerator_isPhaseLinear
    (R : RelationalInformationDatum (E := E)) :
    IsPhaseLinear (E := E)
      (stateGaugeGenerator (E := E) R.modularData R.comparisonState) := by
  simpa [stateGaugeGenerator] using
    (modularGeneratorGaugePart_isPhaseLinear
      (E := E) (R.modularData.modularSeed R.comparisonState))

@[rep_depth transport]
theorem comparisonSourceGenerator_isPhaseAntilinear
    (R : RelationalInformationDatum (E := E)) :
    IsPhaseAntilinear (E := E)
      (stateSourceGenerator (E := E) R.modularData R.comparisonState) := by
  simpa [stateSourceGenerator] using
    (modularGeneratorScalePart_isPhaseAntilinear
      (E := E) (R.modularData.modularSeed R.comparisonState))

@[rep_depth transport, simp]
theorem comparisonGaugeDynamics_eq_transportCommutator_phaseLinearPart
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonGaugeDynamics R A
      =
    transportCommutator (E := E)
      (phaseLinearPart (E := E) (comparisonTransportGenerator R)) A := by
  rfl

@[rep_depth transport, simp]
theorem comparisonSourceDynamics_eq_transportCommutator_phaseAntilinearPart
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonSourceDynamics R A
      =
    transportCommutator (E := E)
      (phaseAntilinearPart (E := E) (comparisonTransportGenerator R)) A := by
  rfl

@[rep_depth transport]
theorem comparisonMetricReadout_eq_metricOfGauge_add_metricOfSource
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonMetricReadout R A
      =
    InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
      (E := E) (comparisonGaugeDynamics R A)
      +
    InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
      (E := E) (comparisonSourceDynamics R A) := by
  ext u v
  rw [comparisonMetricReadout_apply, comparisonInducedDynamics_eq_gauge_add_source]
  rw [InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_add]

@[rep_depth transport]
theorem comparisonMetricReadout_eq_metricOf_phaseLinearPart_add_metricOf_phaseAntilinearPart
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonMetricReadout R A
      =
    InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
      (E := E)
      (transportCommutator (E := E)
        (phaseLinearPart (E := E) (comparisonTransportGenerator R)) A)
      +
    InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
      (E := E)
      (transportCommutator (E := E)
        (phaseAntilinearPart (E := E) (comparisonTransportGenerator R)) A) := by
  rw [comparisonMetricReadout_eq_metricOfGauge_add_metricOfSource]
  rw [comparisonGaugeDynamics_eq_transportCommutator_phaseLinearPart]
  rw [comparisonSourceDynamics_eq_transportCommutator_phaseAntilinearPart]

@[rep_depth transport]
theorem comparisonPhaseReadout_eq_berryOfGauge_add_berryOfSource
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonPhaseReadout R A
      =
    InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
      (E := E) (comparisonGaugeDynamics R A)
      +
    InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
      (E := E) (comparisonSourceDynamics R A) := by
  ext u v
  rw [comparisonPhaseReadout_apply, comparisonInducedDynamics_eq_gauge_add_source]
  rw [InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator_add]

@[rep_depth transport]
theorem comparisonPhaseReadout_eq_berryOf_phaseLinearPart_add_berryOf_phaseAntilinearPart
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonPhaseReadout R A
      =
    InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
      (E := E)
      (transportCommutator (E := E)
        (phaseLinearPart (E := E) (comparisonTransportGenerator R)) A)
      +
    InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
      (E := E)
      (transportCommutator (E := E)
        (phaseAntilinearPart (E := E) (comparisonTransportGenerator R)) A) := by
  rw [comparisonPhaseReadout_eq_berryOfGauge_add_berryOfSource]
  rw [comparisonGaugeDynamics_eq_transportCommutator_phaseLinearPart]
  rw [comparisonSourceDynamics_eq_transportCommutator_phaseAntilinearPart]

/-! ## Thermodynamic floor attached to the `K`-split -/

@[rep_depth transport]
theorem isPotentialKillingOperator_iff_comparisonReadoutStationary
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH) :
    IsPotentialKillingOperator (E := E) P ψ A
      ↔
    (InfoGeometry.Canonical.RelativeModularPotential.comparisonMetricReadout
        (E := E) P ψ A,
      InfoGeometry.Canonical.RelativeModularPotential.comparisonPhaseReadout
        (E := E) P ψ A)
        =
      (0, 0) := by
  simpa [IsThermodynamicReadoutStationary] using
    (isPotentialKillingOperator_iff_isThermodynamicReadoutStationary
      (E := E) P ψ A)

@[rep_depth transport]
theorem comparisonReadout_kSplit_eq_zero_of_isPotentialKillingOperator
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH)
    (hKill : IsPotentialKillingOperator (E := E) P ψ A) :
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E) (stateGaugeDynamics (E := E) P.modularData ψ A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E) (stateSourceDynamics (E := E) P.modularData ψ A)
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E) (stateGaugeDynamics (E := E) P.modularData ψ A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E) (stateSourceDynamics (E := E) P.modularData ψ A) )
      =
    (0, 0) := by
  have hPair :=
    comparisonReadout_pair_eq_zero_of_isPotentialKillingOperator
      (E := E) P ψ A hKill
  have hMetric :
      InfoGeometry.Canonical.RelativeModularPotential.comparisonMetricReadout
        (E := E) P ψ A = 0 := by
    exact congrArg Prod.fst hPair
  have hPhase :
      InfoGeometry.Canonical.RelativeModularPotential.comparisonPhaseReadout
        (E := E) P ψ A = 0 := by
    exact congrArg Prod.snd hPair
  apply Prod.ext
  · rw [← InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_add]
    rw [← stateInducedDynamics_eq_gauge_add_source (E := E) P.modularData ψ A]
    exact hMetric
  · rw [← InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator_add]
    rw [← stateInducedDynamics_eq_gauge_add_source (E := E) P.modularData ψ A]
    exact hPhase

@[rep_depth transport]
theorem comparisonReadout_pair_eq_zero_of_equilibriumSeed
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH)
    (hEq : InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed (E := E) P ψ A) :
    (InfoGeometry.Canonical.RelativeModularPotential.comparisonMetricReadout (E := E) P ψ A,
      InfoGeometry.Canonical.RelativeModularPotential.comparisonPhaseReadout (E := E) P ψ A)
      = (0, 0) := by
  exact
    InfoGeometry.Canonical.SouriauPlanckVector.comparisonReadout_pair_eq_zero_of_equilibriumSeed
      (E := E) hEq

@[rep_depth transport]
theorem comparisonReadout_phasePart_eq_zero_of_isPotentialKillingOperator
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH)
    (hKill : IsPotentialKillingOperator (E := E) P ψ A) :
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (stateRelativeModularGenerator (E := E) P.modularData ψ)) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (stateRelativeModularGenerator (E := E) P.modularData ψ)) A)
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (stateRelativeModularGenerator (E := E) P.modularData ψ)) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (stateRelativeModularGenerator (E := E) P.modularData ψ)) A) )
      =
    (0, 0) := by
  simpa [stateGaugeDynamics, stateSourceDynamics] using
    (comparisonReadout_kSplit_eq_zero_of_isPotentialKillingOperator
      (E := E) P ψ A hKill)

@[rep_depth transport]
theorem comparisonReadout_kSplit_eq_zero_of_equilibriumSeed
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH)
    (hEq : InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed (E := E) P ψ A) :
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E) (stateGaugeDynamics (E := E) P.modularData ψ A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E) (stateSourceDynamics (E := E) P.modularData ψ A)
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E) (stateGaugeDynamics (E := E) P.modularData ψ A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E) (stateSourceDynamics (E := E) P.modularData ψ A) )
      =
    (0, 0) := by
  exact
    comparisonReadout_kSplit_eq_zero_of_isPotentialKillingOperator
      (E := E) P ψ A
      ((isPotentialKillingOperator_iff_comparisonReadoutStationary
        (E := E) P ψ A).2
        (comparisonReadout_pair_eq_zero_of_equilibriumSeed (E := E) P ψ A hEq))

@[rep_depth transport]
theorem comparisonReadout_phasePart_eq_zero_of_equilibriumSeed
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH)
    (hEq : InfoGeometry.Canonical.SouriauPlanckVector.GibbsSouriauEquilibriumSeed (E := E) P ψ A) :
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (stateRelativeModularGenerator (E := E) P.modularData ψ)) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (stateRelativeModularGenerator (E := E) P.modularData ψ)) A)
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (stateRelativeModularGenerator (E := E) P.modularData ψ)) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (stateRelativeModularGenerator (E := E) P.modularData ψ)) A) )
      =
    (0, 0) := by
  simpa [stateGaugeDynamics, stateSourceDynamics] using
    (comparisonReadout_kSplit_eq_zero_of_equilibriumSeed
      (E := E) P ψ A hEq)

@[rep_depth transport]
theorem comparisonReadout_phasePart_eq_zero_of_firstVariation_eq_zero_of_probeFaithful
    (P : InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum (E := E))
    (ψ : H₂) (A : EndH)
    (hFaithful : ProbeFaithful (E := E) P)
    (hFirst : InfoGeometry.Canonical.RelativeModularPotential.firstVariation (E := E) P ψ A = 0) :
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (stateRelativeModularGenerator (E := E) P.modularData ψ)) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (stateRelativeModularGenerator (E := E) P.modularData ψ)) A)
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (stateRelativeModularGenerator (E := E) P.modularData ψ)) A)
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (stateRelativeModularGenerator (E := E) P.modularData ψ)) A) )
      =
    (0, 0) := by
  exact
    comparisonReadout_phasePart_eq_zero_of_isPotentialKillingOperator
      (E := E) P ψ A
      (isPotentialKillingOperator_of_firstVariation_eq_zero_of_probeFaithful
        (E := E) P ψ A hFaithful hFirst)

end Core

end InfoGeometry.Canonical.MajoranaKreinCartanSplit
