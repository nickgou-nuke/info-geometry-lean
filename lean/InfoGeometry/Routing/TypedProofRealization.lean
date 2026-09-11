import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! A typed readout contract from a symmetry group to proof-goal states.

The contract deliberately separates an operator representation from a proof
realization.  It asserts only lawful action on the chosen goal carrier.
-/

namespace InfoGeometry.Routing.TypedProofRealization

structure ProofGoal where
  id : ℕ
  statement : String

structure Action (G : Type*) [Group G] where
  transform : G → ProofGoal → ProofGoal
  map_one : ∀ goal, transform 1 goal = goal
  map_mul : ∀ g h goal, transform (g * h) goal = transform g (transform h goal)

theorem preserves_composition {G : Type*} [Group G]
    (action : Action G) (g h : G) (goal : ProofGoal) :
    action.transform (g * h) goal =
      (action.transform g ∘ action.transform h) goal := by
  exact action.map_mul g h goal

theorem identity_readout {G : Type*} [Group G]
    (action : Action G) (goal : ProofGoal) :
    action.transform 1 goal = goal := by
  exact action.map_one goal

end InfoGeometry.Routing.TypedProofRealization
