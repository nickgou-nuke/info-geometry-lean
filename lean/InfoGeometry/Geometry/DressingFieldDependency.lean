import InfoGeometry.Geometry.DressingField

namespace InfoGeometry.Geometry.DressingField.ProofDependency

inductive Archetype
  | equivariantFrame
  | invariantComposite
  | quotientDescent
  | frameCocycle
  | stabilizerObstruction
  | completeNormalForm
  deriving DecidableEq

private def archetypeEquivFin : Archetype ≃ Fin 6 where
  toFun
    | .equivariantFrame => 0
    | .invariantComposite => 1
    | .quotientDescent => 2
    | .frameCocycle => 3
    | .stabilizerObstruction => 4
    | .completeNormalForm => 5
  invFun
    | 0 => .equivariantFrame
    | 1 => .invariantComposite
    | 2 => .quotientDescent
    | 3 => .frameCocycle
    | 4 => .stabilizerObstruction
    | _ => .completeNormalForm
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype Archetype := Fintype.ofEquiv (Fin 6) archetypeEquivFin.symm

open Archetype

def prerequisites : Archetype → Finset Archetype
  | equivariantFrame => {equivariantFrame}
  | invariantComposite => {equivariantFrame, invariantComposite}
  | quotientDescent => {equivariantFrame, invariantComposite, quotientDescent}
  | frameCocycle => {equivariantFrame, frameCocycle}
  | stabilizerObstruction => {equivariantFrame, stabilizerObstruction}
  | completeNormalForm => {equivariantFrame, invariantComposite, completeNormalForm}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem causal_branches :
    equivariantFrame < invariantComposite ∧ invariantComposite < quotientDescent ∧
      equivariantFrame < frameCocycle ∧ equivariantFrame < stabilizerObstruction ∧
      invariantComposite < completeNormalForm := by
  simp only [lt_iff_le_not_ge]
  decide

theorem descent_and_obstruction_incomparable :
    ¬ quotientDescent ≤ stabilizerObstruction ∧
      ¬ stabilizerObstruction ≤ quotientDescent := by
  decide

theorem no_dependency_cycle {earlier later : Archetype}
    (forward : earlier < later) : ¬ later < earlier := lt_asymm forward

end InfoGeometry.Geometry.DressingField.ProofDependency
