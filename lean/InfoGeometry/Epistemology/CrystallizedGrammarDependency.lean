import InfoGeometry.Epistemology.CrystallizedGrammar

namespace InfoGeometry.Epistemology.CrystallizedGrammar.ProofDependency

inductive Archetype
  | hullGeneration
  | extremePoint
  | endpointSaturation
  | maximizerSet
  | linearSaturation
  | uniqueMaximum
  | generatorMembership
  | convexBound
  | finiteMaximum
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | hullGeneration => {hullGeneration}
  | extremePoint => {extremePoint}
  | endpointSaturation => {endpointSaturation}
  | maximizerSet => {extremePoint, endpointSaturation, maximizerSet}
  | linearSaturation => {endpointSaturation, linearSaturation}
  | uniqueMaximum => {extremePoint, endpointSaturation, uniqueMaximum}
  | generatorMembership =>
      {hullGeneration, extremePoint, endpointSaturation, uniqueMaximum, generatorMembership}
  | convexBound => {hullGeneration, convexBound}
  | finiteMaximum => {hullGeneration, convexBound, finiteMaximum}

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
    extremePoint < uniqueMaximum ∧ uniqueMaximum < generatorMembership ∧
    hullGeneration < generatorMembership ∧ hullGeneration < convexBound ∧
    convexBound < finiteMaximum := by
  simp only [lt_iff_le_not_ge]
  decide

theorem uniqueness_and_finiteness_incomparable :
    ¬ uniqueMaximum ≤ finiteMaximum ∧ ¬ finiteMaximum ≤ uniqueMaximum := by
  decide

theorem saturation_branches :
    endpointSaturation < uniqueMaximum ∧ endpointSaturation < maximizerSet ∧
    extremePoint < maximizerSet ∧ endpointSaturation < linearSaturation ∧
    ¬ maximizerSet ≤ uniqueMaximum ∧ ¬ uniqueMaximum ≤ maximizerSet := by
  simp only [lt_iff_le_not_ge]
  decide

theorem no_cycle {earlier later : Archetype} (forward : earlier < later) :
    ¬ later < earlier := lt_asymm forward

end InfoGeometry.Epistemology.CrystallizedGrammar.ProofDependency
