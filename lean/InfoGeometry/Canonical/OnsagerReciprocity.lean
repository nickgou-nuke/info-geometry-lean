import InfoGeometry.Canonical.RelativeModularPotential
import InfoGeometry.Canonical.RelationalInformationDynamics

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OnsagerReciprocity

Constructive reciprocal-response layer for operatorial relational information
geometry on the doubled carrier.

This file stays in the noncommutative operatorial lane. It formalizes:

- symmetric Onsager coefficients extracted from the primitive relative modular
  potential,
- the skew bracket/curvature companion channel,
- reciprocal symmetry of the concrete comparison-state channel metric,
- and alternation of the phase sector under explicit `K = Jε`-equivariance of
  the perturbation channels.
-/

namespace InfoGeometry.Canonical.OnsagerReciprocity

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelationalInformationDynamics
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Symmetric operatorial response coefficient read by the primitive potential probe. -/
@[rep_depth transport]
noncomputable def responseCoefficient
    (P : PotentialDatum (E := E)) (X Y A : EndH) : ℝ :=
  P.probe
    (InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMetricPart
      (E := E) X Y A)

/-- Skew bracket/curvature response coefficient read by the primitive potential probe. -/
@[rep_depth transport]
noncomputable def curvatureCoefficient
    (P : PotentialDatum (E := E)) (X Y A : EndH) : ℝ :=
  P.probe
    (InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart
      (E := E) X Y A)

/-- The symmetric response coefficient satisfies Onsager reciprocity. -/
@[rep_depth transport]
theorem responseCoefficient_swap
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    responseCoefficient (E := E) P X Y A
      =
    responseCoefficient (E := E) P Y X A := by
  unfold responseCoefficient
  rw [InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMetricPart_swap
    (E := E) X Y A]

/-- The skew bracket/curvature coefficient flips sign when the channels are swapped. -/
@[rep_depth transport]
theorem curvatureCoefficient_swap_neg
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    curvatureCoefficient (E := E) P Y X A
      =
    -curvatureCoefficient (E := E) P X Y A := by
  unfold curvatureCoefficient
  have hSwap :
      InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart
          (E := E) Y X A
        =
      -InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart
          (E := E) X Y A := by
    unfold InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart
    abel
  rw [hSwap]
  simp

/-- The skew coefficient is exactly the probe of the bracket-derivation response. -/
@[rep_depth transport]
theorem curvatureCoefficient_eq_probe_bracketDerivation
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    curvatureCoefficient (E := E) P X Y A
      =
    P.probe
      (InfoGeometry.Canonical.RelationalInformationDynamics.observableLieDerivation
        (E := E) ⁅X, Y⁆ A) := by
  unfold curvatureCoefficient
  rw [InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationCurvaturePart_eq_bracketDerivation
    (E := E) X Y A]

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
    (P : PotentialDatum (E := E)) (reference comparison : H₂)
    (X Y : PerturbationChannel E) :
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
      =
    comparisonGeneratorMetric
        (toRelationalInformationDatum (E := E) P reference comparison) Y X := by
  simp [real_inner_comm]

/--
Under `K = Jε`-equivariance of the perturbation channels, the comparison-state
phase sector is alternating.
-/
@[rep_depth krein]
theorem comparisonGeneratorPhase_swap_neg_of_IsPhaseLinear
    (P : PotentialDatum (E := E)) (reference comparison : H₂)
    (X Y : PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X)
    (hY : IsPhaseLinear (E := E) Y) :
    comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
      =
    -comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) Y X := by
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
    comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) X Y
        =
      ⟪(X.comp (modularComplexI (E := E))) comparison, Y comparison⟫_ℝ := by
          simp
    _ = ⟪modularComplexI (E := E) (X comparison), Y comparison⟫_ℝ := by
          rw [hXeval]
    _ = -⟪X comparison, modularComplexI (E := E) (Y comparison)⟫_ℝ := by
          rw [modularComplexI_inner_skew (E := E) (X comparison) (Y comparison)]
    _ = -⟪X comparison, (Y.comp (modularComplexI (E := E))) comparison⟫_ℝ := by
          rw [← hYeval]
    _ = -⟪(Y.comp (modularComplexI (E := E))) comparison, X comparison⟫_ℝ := by
          rw [real_inner_comm]
    _ =
      -comparisonGeneratorPhase
        (toRelationalInformationDatum (E := E) P reference comparison) Y X := by
          simp

end Core

end InfoGeometry.Canonical.OnsagerReciprocity
