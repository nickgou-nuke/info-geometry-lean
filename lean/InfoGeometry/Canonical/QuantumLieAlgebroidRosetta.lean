import InfoGeometry.Canonical.ThermodynamicGenerator
import InfoGeometry.Canonical.RosettaSourceBridge

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.QuantumLieAlgebroidRosetta

Rosetta bridge from the language of arXiv:2105.01513, *Quantum Systems as Lie
Algebroids*, to the repo-native doubled real operatorial presentation.

This file does not introduce a new Lie-algebroid subsystem. It only records the
checked identification between the paper's standard complex/Kähler vocabulary
and the repository's internal doubled Krein / Majorana language.
-/

namespace InfoGeometry.Canonical.QuantumLieAlgebroidRosetta

open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.ThermodynamicGenerator
open InfoGeometry.Canonical.Rosetta
open InfoGeometry.Krein

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable def internalPhaseAxis : H₂ →L[ℝ] H₂ :=
  InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E)

@[rep_depth krein, simp] theorem internalPhaseAxis_eq_complex_i :
    internalPhaseAxis (E := E) = InfoGeometry.Krein.complex_i (E := E) := by
  simpa [internalPhaseAxis] using
    (InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i (E := E))

/--
Paper complex unit `i` corresponds to the repo's internal real-Majorana phase
axis `K = Jε` on the doubled carrier.
-/
@[rep_depth krein, simp] theorem paper_complexUnit_eq_internalPhaseAxis :
    (internalPhaseAxis (E := E)).toLinearMap =
      (InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore E).K := by
  simpa [internalPhaseAxis_eq_complex_i] using
    complex_i_toLinearMap_eq_realMajoranaKAxis (E := E)

/--
On perturbation channels, the paper's complex multiplication by `i` is realized
as right composition with the internal phase axis `K = Jε`.
-/
@[rep_depth krein, simp] theorem paper_channelPhaseAxis_apply_eq_comp_internalPhaseAxis
    (X : PerturbationChannel E) :
    channelPhaseAxis (E := E) X = X.comp (internalPhaseAxis (E := E)) := by
  simp [channelPhaseAxis_apply, internalPhaseAxis]

/--
The paper's Kähler phase form on perturbation channels is the repo's generator
phase form induced by the same internal phase axis.
-/
@[rep_depth krein, simp] theorem paper_generatorPhase_eq_metric_comp_internalPhaseAxis
    (R : RelationalInformationDatum (E := E)) :
    comparisonGeneratorPhase R
      =
    (comparisonGeneratorMetric R).compLeft (channelPhaseAxis (E := E)) := by
  rfl

/--
The comparison-state Lie-algebroid anchor in the paper's sense is the repo's
comparison-state induced dynamics.
-/
@[rep_depth transport, simp] theorem paper_anchor_eq_comparisonInducedDynamics
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonInducedDynamics R A
      =
    InfoGeometry.Canonical.StateDependentTransport.stateInducedDynamics
      R.modularData R.comparisonState A := by
  rfl

/--
The paper's anchor splits through the repo's Cartan decomposition into
gauge-preserving and source/dilation branches.
-/
@[rep_depth transport, simp] theorem paper_anchor_split_eq_gauge_add_source
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonInducedDynamics R A
      =
    comparisonGaugeDynamics R A + comparisonSourceDynamics R A :=
  comparisonInducedDynamics_eq_gauge_add_source R A

/--
The paper's state-side Schrödinger current is the probe applied to the same
induced dynamics that defines the repo's operatorial anchor.
-/
@[rep_depth transport, simp] theorem paper_schrodingerCurrent_eq_probe_anchor
    (P : PotentialDatum (E := E)) (ψ : H₂) (A : EndH) :
    firstVariation (E := E) P ψ A
      =
    P.probe
      (InfoGeometry.Canonical.StateDependentTransport.stateInducedDynamics
        P.modularData ψ A) :=
  firstVariation_eq_probe_stateInducedDynamics P ψ A

/--
For a relational datum, the paper's metric/symplectic readout pair is the
repo's metric/Berry pair of the comparison-state anchor.
-/
@[rep_depth transport, simp] theorem paper_metricPhase_pair_eq_metricBerry_of_anchor
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) (u v : H₂) :
    ( comparisonMetricReadout R A u v
    , comparisonPhaseReadout R A u v )
      =
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E) (comparisonInducedDynamics R A) u v
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E) (comparisonInducedDynamics R A) u v ) := by
  apply Prod.ext
  · exact RelationalInformationCore.comparisonMetricReadout_apply R A u v
  · exact RelationalInformationCore.comparisonPhaseReadout_apply R A u v

/--
The paper's Kähler phase form on states is the metric readout twisted by the
internal phase axis `K = Jε`, not by an external scalar `i`.
-/
@[rep_depth transport, simp] theorem paper_phaseReadout_eq_metric_comp_internalPhaseAxis
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonPhaseReadout R A
      =
    (comparisonMetricReadout R A).compLeft (internalPhaseAxis (E := E)).toLinearMap := by
  simpa [internalPhaseAxis_eq_complex_i] using
    (RelationalInformationCore.comparisonPhaseReadout_eq_metric_comp_complex_i
      (E := E) R A)

@[rep_depth transport, simp] theorem paper_phaseReadout_eq_metric_comp_complex_i
    (R : RelationalInformationDatum (E := E))
    (A : ObservableAlgebra E) :
    comparisonPhaseReadout R A
      =
    (comparisonMetricReadout R A).compLeft
      (InfoGeometry.Krein.complex_i (E := E)).toLinearMap := by
  simpa [internalPhaseAxis_eq_complex_i] using
    paper_phaseReadout_eq_metric_comp_internalPhaseAxis (E := E) R A

/--
When a relational datum is induced from a primitive potential datum, the paper's
comparison-state anchor is exactly the state-induced dynamics at the chosen
comparison state.
-/
@[rep_depth transport, simp] theorem paper_inducedDatum_anchor_eq_stateInducedDynamics
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (A : EndH) :
    comparisonInducedDynamics
        (toRelationalInformationDatum (E := E) P reference comparison) A
      =
    InfoGeometry.Canonical.StateDependentTransport.stateInducedDynamics
      P.modularData comparison A := by
  rfl

end Core

end InfoGeometry.Canonical.QuantumLieAlgebroidRosetta
