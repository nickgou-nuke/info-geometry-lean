import Mathlib.Data.Finset.Order
import Mathlib.Tactic

namespace InfoGeometry.Twistor.SpinorOuterProduct.ProofDependency

inductive Archetype
  | outerProduct
  | determinantNullity
  | hermitianDiagonal
  | scalarCovariance
  | phaseInvariance
  deriving DecidableEq, Fintype

def prerequisites : Archetype → Finset ℕ
  | .outerProduct => {0}
  | .determinantNullity => {0, 1}
  | .hermitianDiagonal => {0, 2}
  | .scalarCovariance => {0, 3}
  | .phaseInvariance => {0, 3, 4}

theorem prerequisites_injective : Function.Injective prerequisites := by
  decide

instance : PartialOrder Archetype :=
  PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Archetype) (· ≤ ·) :=
  fun left right => inferInstanceAs (Decidable (prerequisites left ⊆ prerequisites right))

theorem determinant_branch :
    Archetype.outerProduct ≤ Archetype.determinantNullity := by decide

theorem hermitian_branch :
    Archetype.outerProduct ≤ Archetype.hermitianDiagonal := by decide

theorem scaling_phase_branch :
    Archetype.outerProduct ≤ Archetype.scalarCovariance ∧
      Archetype.scalarCovariance ≤ Archetype.phaseInvariance := by decide

theorem nullity_and_phase_incomparable :
    ¬ Archetype.determinantNullity ≤ Archetype.phaseInvariance ∧
      ¬ Archetype.phaseInvariance ≤ Archetype.determinantNullity := by decide

theorem hermiticity_and_phase_incomparable :
    ¬ Archetype.hermitianDiagonal ≤ Archetype.phaseInvariance ∧
      ¬ Archetype.phaseInvariance ≤ Archetype.hermitianDiagonal := by decide

theorem no_cycle (left right : Archetype) (forward : left ≤ right)
    (backward : right ≤ left) : left = right :=
  le_antisymm forward backward

end InfoGeometry.Twistor.SpinorOuterProduct.ProofDependency
