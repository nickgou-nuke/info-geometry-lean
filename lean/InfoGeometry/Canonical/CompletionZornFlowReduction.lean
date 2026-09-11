import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Explicit Zorn reduction of a completion flow

This owner records the missing interface between a completed operator algebra
and a chosen Zorn subalgebra.  No embedding, invariant subalgebra, or boost is
constructed here: each is an explicit input.
-/

noncomputable section

namespace InfoGeometry.Canonical.CompletionZornFlowReduction

variable {Z C : Type*}
variable [Ring Z] [Algebra ℂ Z] [StarRing Z]
variable [Ring C] [Algebra ℂ C] [StarRing C]

/-- The algebraic unitary condition used for a star-conjugation boost. -/
def IsStarUnitary (u : Z) : Prop :=
  star u * u = 1 ∧ u * star u = 1

/--
All data needed for a genuine reduction of a completion flow to a Zorn
subalgebra.  The last field is the actual invariance/intertwining input.
-/
structure Data (flow : ℝ → C ≃⋆ₐ[ℂ] C) where
  zornEmbedding : Z →⋆ₐ[ℂ] C
  boost : ℝ → Z
  boost_unitary : ∀ t, IsStarUnitary (boost t)
  restriction : ∀ (t : ℝ) (x : Z),
    flow t (zornEmbedding x) =
      zornEmbedding (boost t * x * star (boost t))

theorem flow_restricts
    {flow : ℝ → C ≃⋆ₐ[ℂ] C} (D : Data (Z := Z) (C := C) flow) (t : ℝ) (x : Z) :
    flow t (D.zornEmbedding x) =
      D.zornEmbedding (D.boost t * x * star (D.boost t)) :=
  D.restriction t x

theorem boost_is_star_unitary
    {flow : ℝ → C ≃⋆ₐ[ℂ] C} (D : Data (Z := Z) (C := C) flow) (t : ℝ) :
    IsStarUnitary (D.boost t) :=
  D.boost_unitary t

end InfoGeometry.Canonical.CompletionZornFlowReduction
