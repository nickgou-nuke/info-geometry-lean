import InfoGeometry.Canonical.ZornCore
import proofs.ZornAssociatorSplitOctonion
import proofs.GrandUnifiedTKK
import InfoGeometry.Canonical.ZornTrialityTKKBridge

/-! Finite triality-form calculations for the split-octonion associator. -/

noncomputable section

namespace ZornTrialityForm

open ZornCore
open ZornAssociatorSplitOctonion
open GrandUnifiedTKK
open ZornTrialityTKKBridge
open TKKJordanPairData

def trialityForm (Φ X Ψ : ZornCore.Zorn) : ZornCore.Zorn :=
  associator Φ X Ψ

theorem trialityForm_eq_associator (Φ X Ψ : ZornCore.Zorn) :
    trialityForm Φ X Ψ = associator Φ X Ψ := by
  rfl

theorem canonical_trialityForm_nonzero :
    trialityForm (U e1) (L e1) (U e2) ≠ 0 := by
  simpa [trialityForm_eq_associator] using mixed_nonassociative

theorem canonical_trialityForm_grade :
    laneGrade SplitOctonionLane.associatorWitness = TKKGrade.p2 := by
  exact laneGrade_associatorWitness

theorem trialityForm_synthesis :
    trialityForm (U e1) (L e1) (U e2) ≠ 0 ∧
    laneGrade SplitOctonionLane.associatorWitness = TKKGrade.p2 := by
  exact ⟨canonical_trialityForm_nonzero, canonical_trialityForm_grade⟩

end ZornTrialityForm
