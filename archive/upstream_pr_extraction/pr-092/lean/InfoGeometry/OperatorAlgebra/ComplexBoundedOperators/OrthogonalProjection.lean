import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# AFP CBO orthogonal-complement and projection adapters

This file exposes the Hilbert-space orthogonal-complement, projection, and
closest-point API in the repository's CBO namespace.  The proofs are direct
wrappers around Mathlib's `Submodule.orthogonal` and `Submodule.starProjection`
theorems.
-/

noncomputable section

open scoped InnerProductSpace

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace OrthogonalProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- AFP `ccsubspace` orthogonal complement, Lean-native as `Submodule.orthogonal`. -/
abbrev orthogonalComplement (K : Submodule ℂ E) : Submodule ℂ E :=
  Kᗮ

theorem mem_orthogonalComplement_iff (K : Submodule ℂ E) (v : E) :
    v ∈ orthogonalComplement K ↔ ∀ u ∈ K, ⟪u, v⟫_ℂ = 0 :=
  K.mem_orthogonal v

theorem mem_orthogonalComplement_iff_left (K : Submodule ℂ E) (v : E) :
    v ∈ orthogonalComplement K ↔ ∀ u ∈ K, ⟪v, u⟫_ℂ = 0 :=
  K.mem_orthogonal' v

theorem orthogonalComplement_closed (K : Submodule ℂ E) :
    IsClosed (orthogonalComplement K : Set E) :=
  K.isClosed_orthogonal

theorem inf_orthogonalComplement_eq_bot (K : Submodule ℂ E) :
    K ⊓ orthogonalComplement K = ⊥ :=
  K.inf_orthogonal_eq_bot

theorem orthogonalComplement_disjoint (K : Submodule ℂ E) :
    Disjoint K (orthogonalComplement K) :=
  K.orthogonal_disjoint

@[simp]
theorem top_orthogonalComplement_eq_bot :
    orthogonalComplement (⊤ : Submodule ℂ E) = ⊥ :=
  Submodule.top_orthogonal_eq_bot

@[simp]
theorem bot_orthogonalComplement_eq_top :
    orthogonalComplement (⊥ : Submodule ℂ E) = ⊤ :=
  Submodule.bot_orthogonal_eq_top

theorem orthogonalComplement_eq_top_iff (K : Submodule ℂ E) :
    orthogonalComplement K = ⊤ ↔ K = ⊥ :=
  K.orthogonal_eq_top_iff

theorem orthogonalComplement_closure (K : Submodule ℂ E) :
    K.topologicalClosureᗮ = Kᗮ :=
  Submodule.orthogonal_closure K

theorem double_orthogonalComplement_eq_closure [CompleteSpace E] (K : Submodule ℂ E) :
    Kᗮᗮ = K.topologicalClosure :=
  K.orthogonal_orthogonal_eq_closure

section Projection

variable (K : Submodule ℂ E) [K.HasOrthogonalProjection]

/-- Orthogonal projection onto a subspace, as an ambient bounded operator. -/
abbrev projection : E →L[ℂ] E :=
  K.starProjection

/-- Orthogonal projection onto a subspace, with codomain the subspace subtype. -/
abbrev projectionToSubmodule : E →L[ℂ] K :=
  K.orthogonalProjection

@[simp]
theorem projection_apply (x : E) :
    projection K x = K.starProjection x :=
  rfl

@[simp]
theorem projectionToSubmodule_apply (x : E) :
    projectionToSubmodule K x = K.orthogonalProjection x :=
  rfl

theorem projection_mem (x : E) :
    projection K x ∈ K := by
  simpa [projection] using Submodule.starProjection_apply_mem (U := K) x

theorem projection_eq_self_iff {x : E} :
    projection K x = x ↔ x ∈ K := by
  simpa [projection] using (K.starProjection_eq_self_iff (v := x))

/-- Closest-point theorem for orthogonal projection. -/
theorem projection_minimal (x : E) :
    ‖x - projection K x‖ = ⨅ y : K, ‖x - y‖ := by
  simpa [projection] using Submodule.starProjection_minimal (U := K) x

theorem projection_range :
    (projection K).range = K := by
  simpa [projection] using Submodule.range_starProjection K

theorem projection_ker :
    (projection K).ker = Kᗮ := by
  simpa [projection] using Submodule.ker_starProjection K

theorem projection_idempotent :
    IsIdempotentElem (projection K) := by
  simpa [projection] using K.isIdempotentElem_starProjection

theorem projection_norm_le (x : E) :
    ‖projection K x‖ ≤ ‖x‖ := by
  simpa [projection] using K.norm_starProjection_apply_le x

theorem projection_split (x : E) :
    K.starProjection x + Kᗮ.starProjection x = x :=
  K.starProjection_add_starProjection_orthogonal x

theorem projection_pythagorean (x : E) :
    ‖x‖ ^ 2 = ‖K.starProjection x‖ ^ 2 + ‖Kᗮ.starProjection x‖ ^ 2 :=
  Submodule.norm_sq_eq_add_norm_sq_starProjection x K

end Projection

end OrthogonalProjection
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators

