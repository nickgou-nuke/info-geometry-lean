import InfoGeometry.Topology.D4StarGraphContinuousAction
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-!
# The faithful topological `S₃` action on the original D₄ star

The quotient action is intentionally trivial, but the action on the original
four-vertex star is not.  These pointwise laws make that distinction explicit
without identifying the star with its coarse orbit quotient.
-/

@[simp] theorem colorPermutationStarAction_identity (v : FourPlaneVertex) :
    (colorPermutationStarAction (1 : Equiv.Perm ColorChannel)).map v = v := by
  cases v <;> rfl

theorem colorPermutationStarAction_comp
    (σ τ : Equiv.Perm ColorChannel) (v : FourPlaneVertex) :
    (colorPermutationStarAction σ).map
        ((colorPermutationStarAction τ).map v) =
      (colorPermutationStarAction (σ * τ)).map v := by
  cases v with
  | inl c =>
      simp [colorPermutationStarAction, vertexPermutationHomeomorph,
        vertexPermutation]
  | inr u =>
      rfl

theorem colorPermutationStarAction_outer_comp
    (σ τ : Equiv.Perm ColorChannel) (c : ColorChannel) :
    (colorPermutationStarAction σ).map
        ((colorPermutationStarAction τ).map (outerVertex c)) =
      outerVertex ((σ * τ) c) := by
  exact colorPermutationStarAction_comp σ τ (outerVertex c)

end InfoGeometry.Topology.PauliJungD4Star
