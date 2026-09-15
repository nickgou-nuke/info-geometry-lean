import InfoGeometry.Geometry.DressingField

namespace InfoGeometry.Geometry.DressingField.ProofDependency

inductive Archetype
  | equivariantFrame
  | invariantComposite
  | quotientDescent
  | frameCocycle
  | stabilizerObstruction
  | completeNormalForm
  deriving DecidableEq, Fintype

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
