import InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1
import InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2
import InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit

Lean-native semantic audit surface for the state-first Chunk1/2/3 lane.

This file provides:
1. explicit axiom-surface print checks for the three chunk capstones,
2. a direct non-vacuity reduction witness (Chunk-2 apex-zero reduction),
3. an admissibility gate witness (Chunk-3 package extraction).
-/

-- Axiom-hygiene surface for the three chunk capstone targets.
#print axioms InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1.stateFirst_modularSplit_singularClosure_operatorialCramerRao
#print axioms InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2.stateFirst_apexZero_activeOnly_operatorialCramerRao
#print axioms InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.stateFirst_admissibleGate_transport_and_operatorialCramerRao

namespace InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk1
open InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2
open InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3

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

end Core

end InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit

