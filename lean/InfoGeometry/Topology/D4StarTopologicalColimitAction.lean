import InfoGeometry.Canonical.ContinuousLeftActionTopCatColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.D4StarTopologicalGroupAction

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ContinuousLeftActionTopCat
open InfoGeometry.Canonical.ContinuousLeftActionTopCatColimit

/-!
# Topological colimit realization of the faithful D₄-star action

This is a topological colimit of the original star action.  It is distinct
from both the coarse orbit quotient and the algebraic star direct limit.
-/

noncomputable def d4StarContinuousLeftAction :
    ContinuousLeftAction (Equiv.Perm ColorChannel) FourPlaneVertex where
  smul σ v := vertexPermutation σ v
  one_smul := by
    intro v
    cases v <;> rfl
  mul_smul := by
    intro σ τ v
    exact (colorPermutationStarAction_comp σ τ v).symm
  continuous_smul := by
    intro σ
    exact continuous_vertexPermutation σ

theorem d4StarContinuousLeftAction_outer
    (σ : Equiv.Perm ColorChannel) (c : ColorChannel) :
    d4StarContinuousLeftAction.smul σ (outerVertex c) =
      outerVertex (σ c) := by
  rfl

theorem d4StarContinuousLeftAction_centre
    (σ : Equiv.Perm ColorChannel) :
    d4StarContinuousLeftAction.smul σ centralVertex = centralVertex := by
  rfl

variable {J : Type} [CategoryTheory.Category J]

abbrev d4StarTopologicalColimitSpace : Type :=
  constantTopDiagramColimitSpace (J := J) (X := FourPlaneVertex)

noncomputable def d4StarTopologicalColimitAction :
    ContinuousLeftAction (Equiv.Perm ColorChannel)
      (d4StarTopologicalColimitSpace (J := J)) :=
  colimitAction (J := J) (X := FourPlaneVertex)
    d4StarContinuousLeftAction

theorem d4StarTopologicalColimitAction_on_stage
    (σ : Equiv.Perm ColorChannel) (j : J) (v : FourPlaneVertex) :
    (d4StarTopologicalColimitAction (J := J)).smul σ
        (CategoryTheory.Limits.colimit.ι
          (constantTopDiagram (J := J) (X := FourPlaneVertex)) j v) =
      CategoryTheory.Limits.colimit.ι
        (constantTopDiagram (J := J) (X := FourPlaneVertex)) j
        (vertexPermutation σ v) := by
  exact colimitAction_apply_stage
    (J := J) (X := FourPlaneVertex) d4StarContinuousLeftAction σ j v

end InfoGeometry.Topology.PauliJungD4Star
