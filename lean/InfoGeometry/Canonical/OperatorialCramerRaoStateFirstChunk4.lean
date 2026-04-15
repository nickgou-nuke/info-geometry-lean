import InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3
import InfoGeometry.Canonical.OperatorialUncertainty
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4

Chunk-4 translation of the state-first/type-III doctrine into repo-native Lean.

This file adds:

1. a strict measurable-operator predicate extending Chunk-3 admissibility with
   a finite-variance bound,
2. closure of that predicate under projector-compressed transport,
3. an uncertainty bridge to the owned operatorial uncertainty surface,
4. a wedge-calibrated package combining measurability, uncertainty, and the
   operatorial Cramér-Rao lower bound.
-/

namespace InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.OperatorialCramerRao
open InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1
open InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance

/--
Strict state-first measurable operator:
Chunk-3 admissibility plus a finite comparison-state variance bound for
an observer channel `X`, with strictly positive variance at the comparison
state.
-/
@[rep_depth transport]
structure MeasurableOperator
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (ψ comparison : H₂)
    (X : PerturbationChannel E) : Prop where
  admissible : StateFirstAdmissibleOperator (E := E) CIK R ψ
  finiteVariance :
    ∃ B : ℝ,
      0 ≤ B
        ∧
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) comparison X X ≤ B
  positiveVariance :
    0 <
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) comparison X X

/-- Constructor helper from explicit admissibility + bound witnesses. -/
@[rep_depth transport]
theorem measurableOperator_mk
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (ψ comparison : H₂)
    (X : PerturbationChannel E)
    (hA : StateFirstAdmissibleOperator (E := E) CIK R ψ)
    (B : ℝ)
    (hBnonneg : 0 ≤ B)
    (hVar : InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
      (E := E) comparison X X ≤ B)
    (hVarPos :
      0 <
        InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
          (E := E) comparison X X) :
    MeasurableOperator (E := E) CIK R ψ comparison X := by
  exact ⟨hA, ⟨B, hBnonneg, hVar⟩, hVarPos⟩

/--
Measurability is stable under projector-compressed operator transport.
-/
@[rep_depth transport]
theorem measurableOperator_projectorCompressed_stable
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (ψ comparison : H₂)
    (X : PerturbationChannel E)
    (hM : MeasurableOperator (E := E) CIK R ψ comparison X) :
    MeasurableOperator
      (E := E)
      CIK
      (projectorCompressed (E := E) CIK R)
      ψ
      comparison
      X := by
  refine ⟨?_, hM.finiteVariance, hM.positiveVariance⟩
  exact
    stateFirstAdmissibleOperator_projectorCompressed_stable
      (E := E) (CIK := CIK) (R := R) (ψ := ψ) hM.admissible

/--
Measurability is stable under modular-flow transport of the state.
-/
@[rep_depth transport]
theorem measurableOperator_modularFlow_state_stable
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (ψ comparison : H₂)
    (X : PerturbationChannel E)
    (hM : MeasurableOperator (E := E) CIK R ψ comparison X)
    (T : InfoGeometry.Canonical.RealTomitaCore.RealModularLogData (E := E))
    (t : ℝ) :
    MeasurableOperator (E := E) CIK R ((T.flow t) ψ) comparison X := by
  refine ⟨?_, hM.finiteVariance, hM.positiveVariance⟩
  exact
    stateFirstAdmissibleOperator_modularFlow_state_stable
      (E := E) (CIK := CIK) (R := R) (ψ := ψ) hM.admissible T t

/--
Bridge to the owned operatorial uncertainty surface:
measurability exposes the spectral commutation witness and grants the
Robertson-Schrödinger channel inequality for phase-linear `X`.
-/
@[rep_depth transport]
theorem measurableOperator_uncertainty_bridge
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (ψ comparison : H₂)
    (X Y : PerturbationChannel E)
    (hM : MeasurableOperator (E := E) CIK R ψ comparison X)
    (hX : InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear X) :
    Commute CIK.spectralProjector R
      ∧
    (InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) comparison X Y) ^ 2
      +
    (InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorPhase
        (E := E) comparison X Y) ^ 2
      ≤
    InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) comparison X X
      *
    InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) comparison Y Y := by
  refine ⟨hM.admissible.1, ?_⟩
  exact
    InfoGeometry.Canonical.OperatorialUncertainty.comparisonStateGeneratorMetric_sq_add_phase_sq_le_of_IsPhaseLinear
      (E := E) comparison X Y hX

/--
Chunk-4 capstone package:
on the wedge-calibrated lane, canonical bounded relative modular representatives
are measurable (strict gate), remain measurable after projector-compressed
transport, satisfy operatorial uncertainty on phase-linear channels, and retain
the Chunk-1 operatorial Cramér-Rao lower bound.
-/
@[rep_depth transport, capstone]
theorem stateFirst_measurable_uncertainty_operatorialCramerRao_package
    (CIK : CertifiedInverseKernel H₂)
    (S : StateFirstCRWitness (E := E) CIK)
    (τ : ℝ)
    (X : PerturbationChannel E)
    (B : ℝ)
    (hBnonneg : 0 ≤ B)
    (hVar :
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison X X ≤ B)
    (hXnonzero : X S.comparison ≠ 0)
    (hX : InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear X) :
    let R :=
      InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
        (E := E) CIK τ
    MeasurableOperator (E := E) CIK R S.comparison S.comparison X
      ∧
    MeasurableOperator
      (E := E)
      CIK
      (projectorCompressed (E := E) CIK R)
      S.comparison
      S.comparison
      X
      ∧
    ((InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison X S.Y) ^ 2
      +
      (InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorPhase
        (E := E) S.comparison X S.Y) ^ 2
      ≤
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison X X
        *
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.Y S.Y)
      ∧
    (1 /
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.Y S.Y
      ≤
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.X S.X) := by
  intro R
  have hA :
      StateFirstAdmissibleOperator (E := E) CIK R S.comparison := by
    exact
      stateFirstAdmissibleOperator_of_wedgeCalibrated
        (E := E) (CIK := CIK) (W := S.W) S.calibrated τ S.comparison
  have hM :
      MeasurableOperator (E := E) CIK R S.comparison S.comparison X := by
    have hVarPos :
        0 <
          InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
            (E := E) S.comparison X X := by
      exact
        comparisonStateGeneratorMetric_self_pos_of_apply_ne_zero
          (E := E) S.comparison X hXnonzero
    exact
      measurableOperator_mk
        (E := E) (CIK := CIK) (R := R) (ψ := S.comparison)
        (comparison := S.comparison) (X := X) hA B hBnonneg hVar hVarPos
  have hMcompressed :
      MeasurableOperator
        (E := E) CIK (projectorCompressed (E := E) CIK R)
        S.comparison S.comparison X := by
    exact measurableOperator_projectorCompressed_stable
      (E := E) (CIK := CIK) (R := R) (ψ := S.comparison)
      (comparison := S.comparison) (X := X) hM
  have hUnc :
      (InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
          (E := E) S.comparison X S.Y) ^ 2
        +
      (InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorPhase
          (E := E) S.comparison X S.Y) ^ 2
        ≤
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
          (E := E) S.comparison X X
          *
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
          (E := E) S.comparison S.Y S.Y := by
    exact
      (measurableOperator_uncertainty_bridge
        (E := E) (CIK := CIK) (R := R) (ψ := S.comparison)
        (comparison := S.comparison) (X := X) (Y := S.Y) hM hX).2
  refine ⟨hM, hMcompressed, hUnc, ?_⟩
  exact
    (stateFirst_modularSplit_singularClosure_operatorialCramerRao
      (E := E) (CIK := CIK) (S := S) τ).2

end Core

end InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4
