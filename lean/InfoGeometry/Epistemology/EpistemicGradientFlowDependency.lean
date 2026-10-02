import InfoGeometry.Epistemology.EpistemicGradientFlow
import InfoGeometry.Epistemology.DiracRelativeEntropyBoundary

namespace InfoGeometry.Epistemology.EpistemicGradientFlow.ProofDependency

inductive Archetype
  | logisticDerivative
  | fenchelNonnegativity
  | relaxation
  | quadraticBound
  | dissipation
  | decayBound
  | equilibriumLimit
  | diracObstruction
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | logisticDerivative => {logisticDerivative}
  | fenchelNonnegativity => {fenchelNonnegativity}
  | relaxation => {logisticDerivative, relaxation}
  | quadraticBound => {logisticDerivative, fenchelNonnegativity, quadraticBound}
  | dissipation => {logisticDerivative, relaxation, dissipation}
  | decayBound =>
      {logisticDerivative, fenchelNonnegativity, relaxation, quadraticBound, decayBound}
  | equilibriumLimit => {logisticDerivative, relaxation, equilibriumLimit}
  | diracObstruction => {diracObstruction}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem analytic_branches :
    logisticDerivative < quadraticBound ∧ fenchelNonnegativity < quadraticBound ∧
      quadraticBound < decayBound ∧ relaxation < decayBound ∧
      relaxation < dissipation ∧ relaxation < equilibriumLimit := by
  simp only [lt_iff_le_not_ge]
  decide

theorem dissipation_and_rate_incomparable :
    ¬ dissipation ≤ decayBound ∧ ¬ decayBound ≤ dissipation := by
  decide

theorem dirac_obstruction_is_separate :
    ¬ diracObstruction ≤ equilibriumLimit ∧ ¬ equilibriumLimit ≤ diracObstruction := by
  decide

theorem no_cycle {earlier later : Archetype} (forward : earlier < later) :
    ¬ later < earlier := lt_asymm forward

end InfoGeometry.Epistemology.EpistemicGradientFlow.ProofDependency
