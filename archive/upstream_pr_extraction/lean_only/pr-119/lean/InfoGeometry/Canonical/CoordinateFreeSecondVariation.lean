import InfoGeometry.Canonical.RelationalInformationDynamics
import InfoGeometry.Canonical.RelativeModularPotential
import InfoGeometry.Canonical.CorrelationSymmetrization
import InfoGeometry.Canonical.AlgebraicStationarity

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CoordinateFreeSecondVariation

Lean-native translation of the coordinate-free second-variation lane.

This file records the strongest statement the current operatorial spine supports:

- the primitive second variation is the nested Lie derivation already owned by
  `operatorInformationMixedSecondVariation` and its diagonal specialization
  `operatorInformationHessian`;
- its symmetric and skew sectors are the algebraic metric/curvature split given
  by `operatorInformationMetricPart` and `operatorInformationCurvaturePart`;
- and the comparison-state metric/phase readouts are derived from the owned
  two-state channel-correlation surface, not introduced as primitive coordinate
  Fisher data.

This deliberately does not encode the stronger CRB / horizon / Planck-scale
interpretation layer. It only fixes the current constructive operatorial
translation into theorem-bearing Lean surfaces.
-/

namespace InfoGeometry.Canonical.CoordinateFreeSecondVariation

open InfoGeometry.Canonical.AlgebraicStationarity
open InfoGeometry.Canonical.CorrelationSymmetrization
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂
local notation "Kop" => InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E)

/-- The skew curvature sector vanishes on the diagonal second-variation slice. -/
@[rep_depth transport, simp]
theorem operatorInformationCurvaturePart_self_eq_zero
    (X A : EndH) :
    operatorInformationCurvaturePart (E := E) X X A = 0 := by
  simpa [operatorInformationCurvaturePartMap_apply] using
    operatorInformationCurvaturePartMap_diag (E := E) A X

/--
On the diagonal slice, the primitive second Lie variation is exactly its
symmetric metric sector.
-/
@[rep_depth transport, simp]
theorem operatorInformationHessian_eq_metricPart_self
    (X A : EndH) :
    operatorInformationHessian (E := E) X A
      =
    operatorInformationMetricPart (E := E) X X A := by
  symm
  simpa [operatorInformationMetricPartMap_apply] using
    operatorInformationMetricPartMap_diag (E := E) A X

/--
The modular curvature operator is the diagonal metric-sector specialization of
the `K = Jε` second Lie variation.
-/
@[rep_depth transport, simp]
theorem modularCurvatureOperator_eq_metricPart_phaseAxis
    (D : EndH) :
    modularCurvatureOperator (E := E) D
      =
    operatorInformationMetricPart (E := E) Kop Kop D := by
  simp [modularCurvatureOperator, operatorInformationHessian_eq_metricPart_self]

@[rep_depth transport, simp]
theorem modularCurvatureOperator_eq_metricPart_complex_i
    (D : EndH) :
    modularCurvatureOperator (E := E) D
      =
    operatorInformationMetricPart (E := E)
      (InfoGeometry.Krein.complex_i (E := E))
      (InfoGeometry.Krein.complex_i (E := E)) D := by
  rw [← InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i]
  exact modularCurvatureOperator_eq_metricPart_phaseAxis (E := E) D

/--
The primitive comparison-state metric/phase pair is exactly the same-state
symmetric / `K`-shifted two-channel correlation pair.
-/
@[rep_depth krein, simp]
theorem comparisonState_metric_phase_pair_eq_correlation_pair
    (comparison : H₂)
    (X Y : PerturbationChannel E) :
    (comparisonStateGeneratorMetric (E := E) comparison X Y,
      comparisonStateGeneratorPhase (E := E) comparison X Y)
      =
    (symmetricTwoStateChannelCorrelation (E := E) comparison comparison X Y,
      phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y) := by
  apply Prod.ext
  · exact comparisonStateGeneratorMetric_eq_symmetricTwoStateChannelCorrelation_self
      (E := E) comparison X Y
  · exact comparisonStateGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self
      (E := E) comparison X Y

/--
For relational data induced from the primitive modular potential, the owned
comparison-state metric/phase pair is exactly the same-state symmetric /
`K`-shifted two-channel correlation pair.
-/
@[rep_depth transport, simp]
theorem toRelationalInformationDatum_metric_phase_pair_eq_correlation_pair
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    (comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X Y,
      comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) X Y)
      =
    (symmetricTwoStateChannelCorrelation (E := E) comparison comparison X Y,
      phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison X Y) := by
  apply Prod.ext
  · exact
      toRelationalInformationDatum_comparisonGeneratorMetric_eq_symmetricTwoStateChannelCorrelation_self
        (E := E) P reference comparison X Y
  · exact
      toRelationalInformationDatum_comparisonGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self
        (E := E) P reference comparison X Y

/--
For a relational datum, the comparison-state metric/phase readout pair is
exactly the operatorial metric/Berry readout of the full comparison-state
induced dynamics.
-/
@[rep_depth transport, simp]
theorem comparisonMetricPhaseReadout_pair_eq_operator_pair
    (R : RelationalInformationDatum (E := E))
    (A : EndH) (u v : H₂) :
    ( InfoGeometry.Canonical.RelationalInformationCore.comparisonMetricReadout
        (E := E) R A u v
    , InfoGeometry.Canonical.RelationalInformationCore.comparisonPhaseReadout
        (E := E) R A u v )
      =
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E) (comparisonInducedDynamics R A) u v
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E) (comparisonInducedDynamics R A) u v ) := by
  apply Prod.ext <;> simp

/--
For relational data induced constructively from the primitive modular potential,
the comparison-state metric/phase readout pair is exactly the operatorial
metric/Berry readout of the full comparison-state induced dynamics.
-/
@[rep_depth transport, simp]
theorem toRelationalInformationDatum_comparisonMetricPhaseReadout_pair_eq_operator_pair
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (A : EndH) (u v : H₂) :
    ( InfoGeometry.Canonical.RelationalInformationCore.comparisonMetricReadout
        (E := E) (toRelationalInformationDatum (E := E) P reference comparison) A u v
    , InfoGeometry.Canonical.RelationalInformationCore.comparisonPhaseReadout
        (E := E) (toRelationalInformationDatum (E := E) P reference comparison) A u v )
      =
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (comparisonInducedDynamics
          (toRelationalInformationDatum (E := E) P reference comparison) A) u v
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (comparisonInducedDynamics
          (toRelationalInformationDatum (E := E) P reference comparison) A) u v ) := by
  apply Prod.ext <;> simp

/--
For a relational datum, the comparison-state metric/phase readout pair
decomposes exactly into the gauge-readout pair plus the source-readout pair.
-/
@[rep_depth transport, simp]
theorem comparisonMetricPhaseReadout_pair_eq_gauge_source_operator_pair
    (R : RelationalInformationDatum (E := E))
    (A : EndH) (u v : H₂) :
    ( InfoGeometry.Canonical.RelationalInformationCore.comparisonMetricReadout
        (E := E) R A u v
    , InfoGeometry.Canonical.RelationalInformationCore.comparisonPhaseReadout
        (E := E) R A u v )
      =
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E) (comparisonGaugeDynamics R A) u v
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E) (comparisonSourceDynamics R A) u v
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E) (comparisonGaugeDynamics R A) u v
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E) (comparisonSourceDynamics R A) u v ) := by
  rw [comparisonMetricPhaseReadout_pair_eq_operator_pair (E := E) (R := R) (A := A) (u := u) (v := v)]
  rw [comparisonInducedDynamics_eq_gauge_add_source (E := E) (R := R) (A := A)]
  simp

/--
For relational data induced constructively from the primitive modular potential,
the comparison-state metric/phase readout pair decomposes exactly into the
gauge-readout pair plus the source-readout pair.
-/
@[rep_depth transport, simp]
theorem toRelationalInformationDatum_comparisonMetricPhaseReadout_pair_eq_gauge_source_operator_pair
    (P : PotentialDatum (E := E))
    (reference comparison : H₂)
    (A : EndH) (u v : H₂) :
    ( InfoGeometry.Canonical.RelationalInformationCore.comparisonMetricReadout
        (E := E) (toRelationalInformationDatum (E := E) P reference comparison) A u v
    , InfoGeometry.Canonical.RelationalInformationCore.comparisonPhaseReadout
        (E := E) (toRelationalInformationDatum (E := E) P reference comparison) A u v )
      =
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (comparisonGaugeDynamics
          (toRelationalInformationDatum (E := E) P reference comparison) A) u v
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (comparisonSourceDynamics
          (toRelationalInformationDatum (E := E) P reference comparison) A) u v
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (comparisonGaugeDynamics
          (toRelationalInformationDatum (E := E) P reference comparison) A) u v
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (comparisonSourceDynamics
          (toRelationalInformationDatum (E := E) P reference comparison) A) u v ) := by
  rw [comparisonMetricPhaseReadout_pair_eq_gauge_source_operator_pair
    (E := E)
    (R := toRelationalInformationDatum (E := E) P reference comparison)
    (A := A) (u := u) (v := v)]

end Core

end InfoGeometry.Canonical.CoordinateFreeSecondVariation
