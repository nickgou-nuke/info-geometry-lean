import InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2
import InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3
import InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit

Lean-native audit/extraction surface for the state-first Chunk1/2/3/4 lane.

This file provides:
1. explicit axiom-surface print checks for the three chunk capstones,
2. a direct non-vacuity reduction witness (Chunk-2 apex-zero reduction),
3. admissibility/measurability extraction witnesses (Chunk-3/4),
4. package aliases for backward-compatible downstream consumers.

This is an audit surface (inspection + extraction), not an internalized
meta-theorem proving axiom-freeness or global non-vacuity.
-/

-- Axiom-hygiene surface for the three chunk capstone targets.
#print axioms InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1.stateFirst_modularSplit_singularClosure_operatorialCramerRao
#print axioms InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2.stateFirst_apexZero_activeOnly_operatorialCramerRao
#print axioms InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.stateFirst_admissibleGate_transport_and_operatorialCramerRao
#print axioms InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4.stateFirst_measurable_uncertainty_operatorialCramerRao_package

namespace InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1
open InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2
open InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3
open InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/--
Audit alias: Chunk-2 non-vacuity reduction to the active block under apex-zero.
-/
@[rep_depth transport]
theorem chunk2_active_only_reduction_audit
    (CIK : CertifiedInverseKernel H₂)
    (S : StateFirstCRWitness (E := E) CIK)
    (hApexZero : CIK.spectralComplementaryProjector = 0)
    (τ : ℝ) :
    InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
      (E := E) CIK τ
        =
    CIK.spectralProjector
      * InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
          (E := E) CIK τ
      * CIK.spectralProjector := by
  exact
    (stateFirst_apexZero_activeOnly_operatorialCramerRao
      (E := E) (CIK := CIK) (S := S) hApexZero τ).1

/--
Audit alias: Chunk-3 admissibility package exposes the flowed/compressed
admissibility witness and preserves the Cramér-Rao bound.
-/
@[rep_depth transport]
theorem chunk3_admissibility_package_audit
    (CIK : CertifiedInverseKernel H₂)
    (S : StateFirstCRWitness (E := E) CIK)
    (τ t : ℝ) :
    let R :=
      InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
        (E := E) CIK τ
    StateFirstAdmissibleOperator (E := E) CIK R S.comparison
      ∧
    StateFirstAdmissibleOperator
      (E := E)
      CIK
      (projectorCompressed (E := E) CIK R)
      ((InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK).flow t
        S.comparison)
      ∧
    (1 /
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.Y S.Y
      ≤
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.X S.X) := by
  exact
    stateFirst_admissibleGate_transport_and_operatorialCramerRao
      (E := E) (CIK := CIK) (S := S) τ t

/--
Audit witness: Chunk-3 base admissibility on the canonical representative.
-/
@[rep_depth transport]
theorem chunk3_admissibility_base_audit
    (CIK : CertifiedInverseKernel H₂)
    (S : StateFirstCRWitness (E := E) CIK)
    (τ t : ℝ) :
    let R :=
      InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
        (E := E) CIK τ
    StateFirstAdmissibleOperator (E := E) CIK R S.comparison := by
  intro R
  exact
    (stateFirst_admissibleGate_transport_and_operatorialCramerRao
      (E := E) (CIK := CIK) (S := S) τ t).1

/--
Audit witness: Chunk-3 compressed/modular-flow admissibility.
-/
@[rep_depth transport]
theorem chunk3_admissibility_compressed_audit
    (CIK : CertifiedInverseKernel H₂)
    (S : StateFirstCRWitness (E := E) CIK)
    (τ t : ℝ) :
    let R :=
      InfoGeometry.Canonical.RelativeModularScaleShapeSplit.canonicalRelativeModularOperator
        (E := E) CIK τ
    StateFirstAdmissibleOperator
      (E := E)
      CIK
      (projectorCompressed (E := E) CIK R)
      ((InfoGeometry.Canonical.ModularSuperchargeClosure.canonicalTomitaLogData (E := E) CIK).flow t
        S.comparison) := by
  intro R
  exact
    (stateFirst_admissibleGate_transport_and_operatorialCramerRao
      (E := E) (CIK := CIK) (S := S) τ t).2.1

/--
Audit witness: Chunk-3 preserves the operatorial Cramér-Rao lower bound.
-/
@[rep_depth transport]
theorem chunk3_cr_lower_bound_audit
    (CIK : CertifiedInverseKernel H₂)
    (S : StateFirstCRWitness (E := E) CIK)
    (τ t : ℝ) :
    (1 /
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.Y S.Y
      ≤
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.X S.X) := by
  exact
    (stateFirst_admissibleGate_transport_and_operatorialCramerRao
      (E := E) (CIK := CIK) (S := S) τ t).2.2

/--
Audit alias: Chunk-4 measurable/uncertainty package extraction.
-/
@[rep_depth transport]
theorem chunk4_measurable_uncertainty_package_audit
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
  exact
    stateFirst_measurable_uncertainty_operatorialCramerRao_package
      (E := E) (CIK := CIK) (S := S) τ X B hBnonneg hVar hXnonzero hX

/--
Audit witness: Chunk-4 base measurable-operator gate on the canonical representative.
-/
@[rep_depth transport]
theorem chunk4_measurable_base_audit
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
    MeasurableOperator (E := E) CIK R S.comparison S.comparison X := by
  intro R
  exact
    (stateFirst_measurable_uncertainty_operatorialCramerRao_package
      (E := E) (CIK := CIK) (S := S) τ X B hBnonneg hVar hXnonzero hX).1

/--
Audit witness: Chunk-4 measurable gate after projector compression.
-/
@[rep_depth transport]
theorem chunk4_measurable_compressed_audit
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
    MeasurableOperator
      (E := E)
      CIK
      (projectorCompressed (E := E) CIK R)
      S.comparison
      S.comparison
      X := by
  intro R
  exact
    (stateFirst_measurable_uncertainty_operatorialCramerRao_package
      (E := E) (CIK := CIK) (S := S) τ X B hBnonneg hVar hXnonzero hX).2.1

/--
Audit witness: Chunk-4 uncertainty inequality payload.
-/
@[rep_depth transport]
theorem chunk4_uncertainty_inequality_audit
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
    (stateFirst_measurable_uncertainty_operatorialCramerRao_package
      (E := E) (CIK := CIK) (S := S) τ X B hBnonneg hVar hXnonzero hX).2.2.1

/--
Audit witness: Chunk-4 preserves the operatorial Cramér-Rao lower bound.
-/
@[rep_depth transport]
theorem chunk4_cr_lower_bound_audit
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
    (1 /
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.Y S.Y
      ≤
      InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorMetric
        (E := E) S.comparison S.X S.X) := by
  exact
    (stateFirst_measurable_uncertainty_operatorialCramerRao_package
      (E := E) (CIK := CIK) (S := S) τ X B hBnonneg hVar hXnonzero hX).2.2.2

end Core

end InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit
