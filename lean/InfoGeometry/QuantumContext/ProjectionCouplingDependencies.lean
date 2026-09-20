import Mathlib.Data.Finset.Order
import Mathlib.Tactic

namespace InfoGeometry.QuantumContext.ProjectionCouplingDependencies

inductive Archetype
  | idempotent
  | fixedRange
  | hiddenKernel
  | uniqueDecomposition
  | symmetricInnerProduct
  | orthogonalDecomposition
  | sectorSwap
  | signedMomentum
  | anticommutation
  | scalarCouplingSquare
  | hamiltonianSquare
  | positiveSoftmax
  | softmaxObstruction
  deriving DecidableEq, Fintype

def prerequisites : Archetype → Finset ℕ
  | .idempotent => {0}
  | .fixedRange => {0, 1}
  | .hiddenKernel => {0, 2}
  | .uniqueDecomposition => {0, 1, 2, 3}
  | .symmetricInnerProduct => {4}
  | .orthogonalDecomposition => {0, 1, 2, 3, 4, 5}
  | .sectorSwap => {6}
  | .signedMomentum => {7}
  | .anticommutation => {6, 7, 8}
  | .scalarCouplingSquare => {9}
  | .hamiltonianSquare => {0, 6, 7, 8, 9, 10}
  | .positiveSoftmax => {11}
  | .softmaxObstruction => {0, 6, 11, 12}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder Archetype :=
  PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := Archetype) (· ≤ ·) :=
  fun left right => inferInstanceAs (Decidable (prerequisites left ⊆ prerequisites right))

theorem projection_dependencies :
    Archetype.fixedRange ≤ Archetype.uniqueDecomposition ∧
      Archetype.hiddenKernel ≤ Archetype.uniqueDecomposition ∧
      Archetype.symmetricInnerProduct ≤ Archetype.orthogonalDecomposition := by decide

theorem coupling_dependencies :
    Archetype.sectorSwap ≤ Archetype.anticommutation ∧
      Archetype.signedMomentum ≤ Archetype.anticommutation ∧
      Archetype.anticommutation ≤ Archetype.hamiltonianSquare ∧
      Archetype.scalarCouplingSquare ≤ Archetype.hamiltonianSquare := by decide

theorem range_and_kernel_incomparable :
    ¬ Archetype.fixedRange ≤ Archetype.hiddenKernel ∧
      ¬ Archetype.hiddenKernel ≤ Archetype.fixedRange := by decide

theorem softmax_does_not_supply_swap :
    ¬ Archetype.sectorSwap ≤ Archetype.positiveSoftmax := by decide

theorem no_cycle (left right : Archetype) (forward : left ≤ right)
    (backward : right ≤ left) : left = right := le_antisymm forward backward

end InfoGeometry.QuantumContext.ProjectionCouplingDependencies
