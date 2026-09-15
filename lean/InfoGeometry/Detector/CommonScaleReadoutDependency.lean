import InfoGeometry.Detector.CommonScaleReadout
import InfoGeometry.EmergentGeometry.HarmonicMeanValue

namespace InfoGeometry.Detector.CommonScaleReadout.ProofDependency

inductive Archetype
  | harmonicMeanValue
  | concentricMeans
  | quadraticScale
  | rootFactorization
  | quotientCancellation
  | inverseSquareModel
  | constantDerivative
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | harmonicMeanValue => {harmonicMeanValue}
  | concentricMeans => {harmonicMeanValue, concentricMeans}
  | quadraticScale => {quadraticScale}
  | rootFactorization => {quadraticScale, rootFactorization}
  | quotientCancellation => {quadraticScale, rootFactorization, quotientCancellation}
  | inverseSquareModel =>
      {quadraticScale, rootFactorization, quotientCancellation, inverseSquareModel}
  | constantDerivative =>
      {quadraticScale, rootFactorization, quotientCancellation, constantDerivative}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem dependency_edges :
    harmonicMeanValue < concentricMeans ∧ quadraticScale < rootFactorization ∧
      rootFactorization < quotientCancellation ∧
      quotientCancellation < inverseSquareModel ∧ quotientCancellation < constantDerivative := by
  simp only [lt_iff_le_not_ge]
  decide

theorem harmonic_and_algebraic_branches_incomparable :
    ¬ concentricMeans ≤ constantDerivative ∧ ¬ constantDerivative ≤ concentricMeans := by
  decide

theorem model_and_derivative_incomparable :
    ¬ inverseSquareModel ≤ constantDerivative ∧ ¬ constantDerivative ≤ inverseSquareModel := by
  decide

end InfoGeometry.Detector.CommonScaleReadout.ProofDependency
