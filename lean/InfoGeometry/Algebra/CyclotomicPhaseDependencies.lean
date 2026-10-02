import Mathlib.Data.Finset.Order
import Mathlib.Tactic

namespace InfoGeometry.Algebra.CyclotomicPhaseDependencies

inductive Archetype
  | primitivePhase
  | polygonBalance
  | coordinateProjectors
  | spectralReadout
  | cornerDecomposition
  | nilpotentCorners
  deriving DecidableEq, Fintype

def prerequisites : Archetype → Finset ℕ
  | .primitivePhase => {0}
  | .polygonBalance => {0, 1}
  | .coordinateProjectors => {2}
  | .spectralReadout => {0, 2, 3}
  | .cornerDecomposition => {0, 2, 3, 4}
  | .nilpotentCorners => {0, 2, 3, 4, 5}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Archetype :=
  PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Archetype) (· ≤ ·) :=
  fun left right => inferInstanceAs (Decidable (prerequisites left ⊆ prerequisites right))

theorem phase_branch : Archetype.primitivePhase ≤ Archetype.polygonBalance := by decide

theorem projector_branch :
    Archetype.coordinateProjectors ≤ Archetype.spectralReadout ∧
      Archetype.spectralReadout ≤ Archetype.cornerDecomposition ∧
      Archetype.cornerDecomposition ≤ Archetype.nilpotentCorners := by decide

theorem balance_and_projectors_incomparable :
    ¬ Archetype.polygonBalance ≤ Archetype.coordinateProjectors ∧
      ¬ Archetype.coordinateProjectors ≤ Archetype.polygonBalance := by decide

theorem no_cycle (left right : Archetype) (forward : left ≤ right)
    (backward : right ≤ left) : left = right := le_antisymm forward backward

end InfoGeometry.Algebra.CyclotomicPhaseDependencies
