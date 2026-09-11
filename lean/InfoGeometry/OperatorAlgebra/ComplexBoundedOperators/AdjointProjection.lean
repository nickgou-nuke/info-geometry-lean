import Mathlib.Analysis.InnerProductSpace.Adjoint
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Basic
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.Basic

/-!
# CBO-004: adjoints and orthogonal projections

AFP surface:

* `adj`;
* `adj_cblinfun_compose`;
* `selfadjoint`;
* `is_Proj`;
* `Proj S`.

Lean owner surface:

* `ContinuousLinearMap.adjoint`;
* `IsSelfAdjoint`;
* `Submodule.starProjection`;
* `IsStarProjection`.
-/

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace AdjointProjection

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [InnerProductSpace ℂ G]

/-- AFP `adj`: the Hilbert-space adjoint of a bounded operator. -/
def adjointOp [CompleteSpace E] [CompleteSpace F] (T : E →L[ℂ] F) : F →L[ℂ] E :=
  ContinuousLinearMap.adjoint T

@[simp]
theorem adjointOp_apply_inner [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℂ] F) (x : E) (y : F) :
    ⟪x, adjointOp T y⟫_ℂ = ⟪T x, y⟫_ℂ := by
  exact ContinuousLinearMap.adjoint_inner_right T x y

/-- AFP `adj_cblinfun_compose`. -/
theorem adjointOp_comp [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    (S : F →L[ℂ] G) (T : E →L[ℂ] F) :
    adjointOp (S.comp T) = (adjointOp T).comp (adjointOp S) := by
  exact ContinuousLinearMap.adjoint_comp S T

@[simp]
theorem adjointOp_id [CompleteSpace E] :
    adjointOp (ContinuousLinearMap.id ℂ E) = ContinuousLinearMap.id ℂ E := by
  exact ContinuousLinearMap.adjoint_id

/-- Self-adjointness as `star T = T`. -/
abbrev SelfAdjointOp [CompleteSpace E] (T : E →L[ℂ] E) : Prop :=
  IsSelfAdjoint T

/-- Orthogonal projection onto a submodule with a projection. -/
def orthogonalProjection [CompleteSpace E]
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] : E →L[ℂ] E :=
  U.starProjection

/-- Orthogonal projections are self-adjoint. -/
theorem orthogonalProjection_selfAdjoint [CompleteSpace E]
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    IsSelfAdjoint (orthogonalProjection U) :=
  IsStarProjection.isSelfAdjoint (_root_.isStarProjection_starProjection (U := U))

/-- Orthogonal projections are star projections. -/
theorem orthogonalProjection_isStarProjection [CompleteSpace E]
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    IsStarProjection (orthogonalProjection U) :=
  _root_.isStarProjection_starProjection

end AdjointProjection
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
