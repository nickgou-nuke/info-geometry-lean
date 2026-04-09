import InfoGeometry.Canonical.RelativeModularPotential
import InfoGeometry.Canonical.RelationalInformationDynamics
import InfoGeometry.Canonical.MajoranaKreinCartanSplit
open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OnsagerReciprocity

Constructive reciprocal-response layer for operatorial relational information
geometry on the doubled carrier.

This file stays in the noncommutative operatorial lane. It formalizes:

- the operatorial mixed second-variation bilinear form on perturbation channels,
- its symmetric metric sector, skew curvature sector, and `K = Jε`-twisted phase sector,
- symmetric Onsager coefficients extracted from the primitive relative modular
  potential,
- the skew bracket/curvature companion channel,
- reciprocal symmetry of the concrete comparison-state channel metric,
- and alternation of the phase sector under explicit `K = Jε`-equivariance of
  the perturbation channels.
-/

namespace InfoGeometry.Canonical.OnsagerReciprocity

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.MajoranaKreinCartanSplit
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.StateDependentTransport
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/--
Primitive operatorial second-variation form on perturbation channels, read by
the probe carried in the relative modular potential datum.
-/
@[rep_depth transport]
noncomputable def operatorSecondVariationForm
    (P : PotentialDatum (E := E)) (A : EndH) :
    LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  (operatorInformationMixedSecondVariationMap (E := E) A).compr₂ P.probe

@[rep_depth transport, simp] theorem operatorSecondVariationForm_apply
    (P : PotentialDatum (E := E)) (A : EndH) (X Y : PerturbationChannel E) :
    operatorSecondVariationForm (E := E) P A X Y
      =
    P.probe (operatorInformationMixedSecondVariation (E := E) X Y A) := by
  simp [operatorSecondVariationForm, operatorInformationMixedSecondVariationMap_apply]

/-- Symmetric operatorial Hessian form on perturbation channels. -/
@[rep_depth transport]
noncomputable def operatorMetricHessianForm
    (P : PotentialDatum (E := E)) (A : EndH) :
    LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  (operatorInformationMetricPartMap (E := E) A).compr₂ P.probe

/-- Skew operatorial curvature form on perturbation channels. -/
@[rep_depth transport]
noncomputable def operatorCurvatureHessianForm
    (P : PotentialDatum (E := E)) (A : EndH) :
    LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  (operatorInformationCurvaturePartMap (E := E) A).compr₂ P.probe

/-- `K = Jε`-twisted operatorial phase Hessian form on perturbation channels. -/
@[rep_depth transport]
noncomputable def operatorPhaseHessianForm
    (P : PotentialDatum (E := E)) (A : EndH) :
    LinearMap.BilinForm ℝ (PerturbationChannel E) :=
  (operatorMetricHessianForm (E := E) P A).compLeft channelPhaseAxis

@[rep_depth transport, simp] theorem operatorMetricHessianForm_apply
    (P : PotentialDatum (E := E)) (A : EndH) (X Y : PerturbationChannel E) :
    operatorMetricHessianForm (E := E) P A X Y
      =
    P.probe (operatorInformationMetricPart (E := E) X Y A) := by
  simp [operatorMetricHessianForm, operatorInformationMetricPartMap_apply]

@[rep_depth transport, simp] theorem operatorCurvatureHessianForm_apply
    (P : PotentialDatum (E := E)) (A : EndH) (X Y : PerturbationChannel E) :
    operatorCurvatureHessianForm (E := E) P A X Y
      =
    P.probe (operatorInformationCurvaturePart (E := E) X Y A) := by
  simp [operatorCurvatureHessianForm, operatorInformationCurvaturePartMap_apply]

@[rep_depth transport, simp] theorem operatorPhaseHessianForm_apply
    (P : PotentialDatum (E := E)) (A : EndH) (X Y : PerturbationChannel E) :
    operatorPhaseHessianForm (E := E) P A X Y
      =
    operatorMetricHessianForm (E := E) P A (channelPhaseAxis X) Y := rfl

@[rep_depth transport, simp] theorem operatorPhaseHessianForm_eq_metric_comp_channelPhaseAxis
    (P : PotentialDatum (E := E)) (A : EndH) :
    operatorPhaseHessianForm (E := E) P A
      =
    (operatorMetricHessianForm (E := E) P A).compLeft channelPhaseAxis := rfl

@[rep_depth transport, simp] theorem operatorMetricHessianForm_swap
    (P : PotentialDatum (E := E)) (A : EndH) (X Y : PerturbationChannel E) :
    operatorMetricHessianForm (E := E) P A X Y
      =
    operatorMetricHessianForm (E := E) P A Y X := by
  simp [operatorMetricHessianForm_apply,
    RelationalInformationDynamics.operatorInformationMetricPart_swap]

@[rep_depth transport, simp] theorem operatorCurvatureHessianForm_swap_neg
    (P : PotentialDatum (E := E)) (A : EndH) (X Y : PerturbationChannel E) :
    operatorCurvatureHessianForm (E := E) P A Y X
      =
    -operatorCurvatureHessianForm (E := E) P A X Y := by
  simp [operatorCurvatureHessianForm_apply, operatorInformationCurvaturePart]

@[rep_depth transport, simp] theorem operatorMetricHessianForm_diag
    (P : PotentialDatum (E := E)) (A X : EndH) :
    operatorMetricHessianForm (E := E) P A X X
      =
    P.probe (operatorInformationHessian (E := E) X A) := by
  simp [operatorMetricHessianForm, operatorInformationMetricPartMap_diag]

@[rep_depth transport, simp] theorem operatorCurvatureHessianForm_diag
    (P : PotentialDatum (E := E)) (A X : EndH) :
    operatorCurvatureHessianForm (E := E) P A X X = 0 := by
  simp [operatorCurvatureHessianForm, operatorInformationCurvaturePartMap_diag]

/-- Symmetric operatorial response coefficient read by the primitive potential probe. -/
@[rep_depth transport]
noncomputable def responseCoefficient
    (P : PotentialDatum (E := E)) (X Y A : EndH) : ℝ :=
  operatorMetricHessianForm (E := E) P A X Y

/-- Skew bracket/curvature response coefficient read by the primitive potential probe. -/
@[rep_depth transport]
noncomputable def curvatureCoefficient
    (P : PotentialDatum (E := E)) (X Y A : EndH) : ℝ :=
  operatorCurvatureHessianForm (E := E) P A X Y

/-- The symmetric response coefficient satisfies Onsager reciprocity. -/
@[rep_depth transport]
theorem responseCoefficient_swap
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    responseCoefficient (E := E) P X Y A
      =
    responseCoefficient (E := E) P Y X A := by
  simpa [responseCoefficient] using
    operatorMetricHessianForm_swap (E := E) P A X Y

/-- The skew bracket/curvature coefficient flips sign when the channels are swapped. -/
@[rep_depth transport]
theorem curvatureCoefficient_swap_neg
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    curvatureCoefficient (E := E) P Y X A
      =
    -curvatureCoefficient (E := E) P X Y A := by
  simpa [curvatureCoefficient] using
    operatorCurvatureHessianForm_swap_neg (E := E) P A X Y

/-- The skew coefficient is exactly the probe of the bracket-derivation response. -/
@[rep_depth transport]
theorem curvatureCoefficient_eq_probe_bracketDerivation
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    curvatureCoefficient (E := E) P X Y A
      =
    P.probe
      (InfoGeometry.Canonical.RelationalInformationDynamics.observableLieDerivation
        (E := E) ⁅X, Y⁆ A) := by
  rw [show curvatureCoefficient (E := E) P X Y A
        = P.probe (operatorInformationCurvaturePart (E := E) X Y A) by
          simp [curvatureCoefficient]]
  rw [operatorInformationCurvaturePart_eq_bracketDerivation (E := E) X Y A]

/-- Channel correlation at a fixed state is symmetric. -/
@[rep_depth krein]
theorem channelCorrelationAtState_swap
    (ψ : H₂) (X Y : PerturbationChannel E) :
    channelCorrelationAtState (E := E) ψ X Y
      =
    channelCorrelationAtState (E := E) ψ Y X := by
  simp [channelCorrelationAtState_apply, real_inner_comm]

/-- The concrete comparison-state generator metric is reciprocal. -/
@[rep_depth krein]
theorem comparisonGeneratorMetric_swap
    (comparison : H₂)
    (X Y : PerturbationChannel E) :
    comparisonStateGeneratorMetric comparison X Y
      =
    comparisonStateGeneratorMetric comparison Y X := by
  simp [comparisonStateGeneratorMetric_apply, real_inner_comm]

/--
Under `K = Jε`-equivariance of the perturbation channels, the comparison-state
phase sector is alternating.
-/
@[rep_depth krein]
theorem comparisonGeneratorPhase_swap_neg_of_IsPhaseLinear
    (comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X)
    (hY : IsPhaseLinear (E := E) Y) :
    comparisonStateGeneratorPhase comparison X Y
      =
    -comparisonStateGeneratorPhase comparison Y X := by
  have hXeval :
      (X.comp (modularComplexI (E := E))) comparison
        =
      modularComplexI (E := E) (X comparison) := by
    simpa [IsPhaseLinear, ContinuousLinearMap.comp_apply] using
      congrArg (fun T : EndH => T comparison) hX
  have hYeval :
      (Y.comp (modularComplexI (E := E))) comparison
        =
      modularComplexI (E := E) (Y comparison) := by
    simpa [IsPhaseLinear, ContinuousLinearMap.comp_apply] using
      congrArg (fun T : EndH => T comparison) hY
  calc
    comparisonStateGeneratorPhase comparison X Y
        =
      ⟪(X.comp (modularComplexI (E := E))) comparison, Y comparison⟫_ℝ := by
          simp [comparisonStateGeneratorPhase_apply]
    _ = ⟪modularComplexI (E := E) (X comparison), Y comparison⟫_ℝ := by
          rw [hXeval]
    _ = -⟪X comparison, modularComplexI (E := E) (Y comparison)⟫_ℝ := by
          rw [modularComplexI_inner_skew (E := E) (X comparison) (Y comparison)]
    _ = -⟪X comparison, (Y.comp (modularComplexI (E := E))) comparison⟫_ℝ := by
          rw [← hYeval]
    _ = -⟪(Y.comp (modularComplexI (E := E))) comparison, X comparison⟫_ℝ := by
          rw [real_inner_comm]
    _ =
      -comparisonStateGeneratorPhase comparison Y X := by
          simp [comparisonStateGeneratorPhase_apply]

/-! ## `K`-split bridge for the reciprocity consumer -/

@[rep_depth transport]
theorem toRelationalInformationDatum_comparisonTransportGenerator_eq_gauge_add_source
    (P : PotentialDatum (E := E)) (reference comparison : H₂) :
    comparisonTransportGenerator
        (toRelationalInformationDatum (E := E) P reference comparison)
      =
    stateGaugeGenerator P.modularData comparison
      +
    stateSourceGenerator P.modularData comparison := by
  simpa [toRelationalInformationDatum] using
    (comparisonTransportGenerator_eq_gauge_add_source
      (E := E) (toRelationalInformationDatum (E := E) P reference comparison))

@[rep_depth transport, simp]
theorem toRelationalInformationDatum_comparisonGaugeGenerator_eq_phaseLinearPart
    (P : PotentialDatum (E := E)) (reference comparison : H₂) :
    stateGaugeGenerator P.modularData comparison
      =
    phaseLinearPart (E := E)
      (comparisonTransportGenerator
        (toRelationalInformationDatum (E := E) P reference comparison)) := by
  simpa [toRelationalInformationDatum] using
    (comparisonGaugeGenerator_eq_phaseLinearPart_comparisonTransportGenerator
      (E := E) (toRelationalInformationDatum (E := E) P reference comparison))

@[rep_depth transport, simp]
theorem toRelationalInformationDatum_comparisonSourceGenerator_eq_phaseAntilinearPart
    (P : PotentialDatum (E := E)) (reference comparison : H₂) :
    stateSourceGenerator P.modularData comparison
      =
    phaseAntilinearPart (E := E)
      (comparisonTransportGenerator
        (toRelationalInformationDatum (E := E) P reference comparison)) := by
  simpa [toRelationalInformationDatum] using
    (comparisonSourceGenerator_eq_phaseAntilinearPart_comparisonTransportGenerator
      (E := E) (toRelationalInformationDatum (E := E) P reference comparison))

@[rep_depth transport]
theorem toRelationalInformationDatum_comparisonMetricReadout_eq_metricOf_phaseLinearPart_add_metricOf_phaseAntilinearPart
    (P : PotentialDatum (E := E)) (reference comparison : H₂) (A : EndH) :
    InfoGeometry.Canonical.RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference comparison) A
      =
    InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
      (E := E)
      (transportCommutator (E := E)
        (phaseLinearPart (E := E)
          (comparisonTransportGenerator
            (toRelationalInformationDatum (E := E) P reference comparison))) A)
      +
    InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
      (E := E)
      (transportCommutator (E := E)
        (phaseAntilinearPart (E := E)
          (comparisonTransportGenerator
            (toRelationalInformationDatum (E := E) P reference comparison))) A) := by
  exact comparisonMetricReadout_eq_metricOf_phaseLinearPart_add_metricOf_phaseAntilinearPart
    (E := E) (toRelationalInformationDatum (E := E) P reference comparison) A

@[rep_depth transport]
theorem toRelationalInformationDatum_comparisonPhaseReadout_eq_berryOf_phaseLinearPart_add_berryOf_phaseAntilinearPart
    (P : PotentialDatum (E := E)) (reference comparison : H₂) (A : EndH) :
    InfoGeometry.Canonical.RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference comparison) A
      =
    InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
      (E := E)
      (transportCommutator (E := E)
        (phaseLinearPart (E := E)
          (comparisonTransportGenerator
            (toRelationalInformationDatum (E := E) P reference comparison))) A)
      +
    InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
      (E := E)
      (transportCommutator (E := E)
        (phaseAntilinearPart (E := E)
          (comparisonTransportGenerator
            (toRelationalInformationDatum (E := E) P reference comparison))) A) := by
  exact comparisonPhaseReadout_eq_berryOf_phaseLinearPart_add_berryOf_phaseAntilinearPart
    (E := E) (toRelationalInformationDatum (E := E) P reference comparison) A

@[rep_depth transport]
theorem toRelationalInformationDatum_comparisonMetricPhaseReadout_pair_eq_phaseLinearAntilinear_operator_pair
    (P : PotentialDatum (E := E)) (reference comparison : H₂) (A : EndH) (u v : H₂) :
    ( InfoGeometry.Canonical.RelationalInformationCore.comparisonMetricReadout
        (toRelationalInformationDatum (E := E) P reference comparison) A u v
    , InfoGeometry.Canonical.RelationalInformationCore.comparisonPhaseReadout
        (toRelationalInformationDatum (E := E) P reference comparison) A u v )
      =
    ( InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (comparisonTransportGenerator
              (toRelationalInformationDatum (E := E) P reference comparison))) A) u v
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (comparisonTransportGenerator
              (toRelationalInformationDatum (E := E) P reference comparison))) A) u v
    , InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseLinearPart (E := E)
            (comparisonTransportGenerator
              (toRelationalInformationDatum (E := E) P reference comparison))) A) u v
        +
      InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
        (E := E)
        (transportCommutator (E := E)
          (phaseAntilinearPart (E := E)
            (comparisonTransportGenerator
              (toRelationalInformationDatum (E := E) P reference comparison))) A) u v ) := by
  apply Prod.ext
  · simpa using
      congrArg (fun B : LinearMap.BilinForm ℝ H₂ => B u v)
        (toRelationalInformationDatum_comparisonMetricReadout_eq_metricOf_phaseLinearPart_add_metricOf_phaseAntilinearPart
          (E := E) P reference comparison A)
  · simpa using
      congrArg (fun B : LinearMap.BilinForm ℝ H₂ => B u v)
        (toRelationalInformationDatum_comparisonPhaseReadout_eq_berryOf_phaseLinearPart_add_berryOf_phaseAntilinearPart
          (E := E) P reference comparison A)

end Core

end InfoGeometry.Canonical.OnsagerReciprocity
