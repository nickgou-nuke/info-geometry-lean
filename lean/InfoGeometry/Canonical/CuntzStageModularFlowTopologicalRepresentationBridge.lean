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
variable (Φ : CuntzStageModularFlowData Stage)
variable (hmap_naturality :
  ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
    T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
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

def flowRepresentationData :
    CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationFlow.Data
      Stage (CuntzStageModularFlowTopologicalColimit.system Stage T) (B := B) where
  sourceFlow := modularFlowTopologicalColimitMap Stage T Φ hmap_naturality
  targetFlow := fun _ => 𝟙 (TopCat.of B)

def flowRepresentationStageCovariance
    (hι_comm : ∀ {m n : ℕ} (hmn : m ≤ n),
      (R.realization.ι n).comp
          ((CuntzStageModularFlowTopologicalColimit.system Stage T).map hmn) =
        R.realization.ι m)
    (hcontinuous_ι : ∀ n : ℕ, Continuous (R.realization.ι n)) :
    ∀ (t : ℝ) (n : ℕ),
      topologicalInjection Stage
          (CuntzStageModularFlowTopologicalColimit.system Stage T) n ≫
          (flowRepresentationData (B := B) Stage T Φ hmap_naturality).sourceFlow t ≫
          topologicalRepresentation
            (Stage := Stage)
            (sys := CuntzStageModularFlowTopologicalColimit.system Stage T)
            (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R)
            hι_comm
            hcontinuous_ι =
        topologicalInjection Stage
          (CuntzStageModularFlowTopologicalColimit.system Stage T) n ≫
          topologicalRepresentation
            (Stage := Stage)
            (sys := CuntzStageModularFlowTopologicalColimit.system Stage T)
            (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R)
            hι_comm
            hcontinuous_ι ≫
          (flowRepresentationData (B := B) Stage T Φ hmap_naturality).targetFlow t := by
    intro t n
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    rw [TopCat.comp_app]
    change topologicalRepresentation
        (Stage := Stage)
        (sys := CuntzStageModularFlowTopologicalColimit.system Stage T)
        (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R)
        hι_comm
        hcontinuous_ι
        (modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t
          (topologicalInjection
            Stage (CuntzStageModularFlowTopologicalColimit.system Stage T)
            n a)) =
      topologicalRepresentation
        (Stage := Stage)
        (sys := CuntzStageModularFlowTopologicalColimit.system Stage T)
        (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R)
        hι_comm
        hcontinuous_ι
        (topologicalInjection
          Stage (CuntzStageModularFlowTopologicalColimit.system Stage T)
          n a)
    rw [modularFlowTopologicalColimitMap_inclusion,
      topologicalRepresentation_of_stage,
      topologicalRepresentation_of_stage]
    exact R.invariant n t a

theorem modularFlow_intertwines_invariant_representation
    (hι_comm : ∀ {m n : ℕ} (hmn : m ≤ n),
      (R.realization.ι n).comp
          ((CuntzStageModularFlowTopologicalColimit.system Stage T).map hmn) =
        R.realization.ι m)
    (hcontinuous_ι : ∀ n : ℕ, Continuous (R.realization.ι n))
    (t : ℝ) :
    modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t ≫
        topologicalRepresentation
          (Stage := Stage)
          (sys := CuntzStageModularFlowTopologicalColimit.system Stage T)
          (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R)
          hι_comm
          hcontinuous_ι =
      topologicalRepresentation
          (Stage := Stage)
          (sys := CuntzStageModularFlowTopologicalColimit.system Stage T)
          (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R)
          hι_comm
          hcontinuous_ι ≫
        (flowRepresentationData (B := B) Stage T Φ hmap_naturality).targetFlow t := by
  have h := representation_intertwines_flow
    Stage (CuntzStageModularFlowTopologicalColimit.system Stage T)
    (representationCocone (Stage := Stage) (T := T) (Φ := Φ) R)
        (flowRepresentationData (B := B) Stage T Φ hmap_naturality)
    hι_comm
    hcontinuous_ι
    (flowRepresentationStageCovariance (B := B) (Stage := Stage) (T := T) (Φ := Φ)
      (hmap_naturality := hmap_naturality) (R := R) hι_comm hcontinuous_ι) t
  simpa using h

end InfoGeometry.Canonical.CuntzStageModularFlowTopologicalRepresentationBridge
