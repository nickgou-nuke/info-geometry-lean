import InfoGeometry.Canonical.CuntzStageModularFlowTopologicalColimit
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalRepresentationFlow
import InfoGeometry.Canonical.FilteredStarAlgebraDirectLimitTopologicalRealization

/-!
# Invariant Cuntz modular flow and topological representation readout

An invariant continuous star-algebra realization turns the existing stagewise
Cuntz modular flow into a concrete instance of the generic
flow/representation-intertwining theorem.  The target flow is the identity;
no analytic modular representation is inferred.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.CuntzStageModularFlowTopologicalRepresentationBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzStageModularFlow
open InfoGeometry.Canonical.CuntzStageModularFlowTopologicalColimit
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalRealization
open CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationTransport
open CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationFlow
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open FilteredColimit.Native.Topological

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)
variable (Φ : CuntzStageModularFlowData Stage T)
variable {B : Type} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

structure InvariantRealization where
  realization : TopologicalRealization
    (Stage := Stage) (sys := CuntzStageModularFlowTopologicalColimit.system Stage T)
    (B := B)
  invariant : ∀ (n : ℕ) (t : ℝ) (a : Stage n),
    realization.ι n (Φ.flow n t a) = realization.ι n a

variable (R : InvariantRealization
  (Stage := Stage) (T := T) (Φ := Φ) (B := B))

def representationCocone :
    ContinuousStarRepresentationCocone
      (Stage := Stage)
      (sys := CuntzStageModularFlowTopologicalColimit.system Stage T)
      (B := B) where
  ι := R.realization.ι
  ι_comm := R.realization.ι_comm
  continuous_ι := R.realization.continuous_ι

def flowRepresentationData :
    CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationFlow.Data
      Stage (CuntzStageModularFlowTopologicalColimit.system Stage T)
      (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R) where
  sourceFlow := modularFlowTopologicalColimitMap Stage T Φ
  targetFlow := fun _ => 𝟙 (TopCat.of B)
  stage_covariance := by
    intro t n
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    rw [TopCat.comp_app]
    change topologicalRepresentation
        (Stage := Stage)
        (sys := CuntzStageModularFlowTopologicalColimit.system Stage T)
        (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R)
        (modularFlowTopologicalColimitMap Stage T Φ t
          (topologicalInjection
            Stage (CuntzStageModularFlowTopologicalColimit.system Stage T)
            n a)) =
      topologicalRepresentation
        (Stage := Stage)
        (sys := CuntzStageModularFlowTopologicalColimit.system Stage T)
        (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R)
        (topologicalInjection
          Stage (CuntzStageModularFlowTopologicalColimit.system Stage T)
          n a)
    rw [modularFlowTopologicalColimitMap_inclusion,
      topologicalRepresentation_of_stage,
      topologicalRepresentation_of_stage]
    exact R.invariant n t a

theorem modularFlow_intertwines_invariant_representation (t : ℝ) :
    modularFlowTopologicalColimitMap Stage T Φ t ≫
        topologicalRepresentation
          (Stage := Stage)
          (sys := CuntzStageModularFlowTopologicalColimit.system Stage T)
          (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R) =
      topologicalRepresentation
          (Stage := Stage)
          (sys := CuntzStageModularFlowTopologicalColimit.system Stage T)
          (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R) := by
  have h := representation_intertwines_flow
    Stage (CuntzStageModularFlowTopologicalColimit.system Stage T)
    (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R)
    (flowRepresentationData Stage T Φ R) t
  simpa using h

end InfoGeometry.Canonical.CuntzStageModularFlowTopologicalRepresentationBridge
