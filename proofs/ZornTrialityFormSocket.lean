import InfoGeometry.Canonical.ZornCore
import proofs.ZornAssociatorSplitOctonion
import proofs.GrandUnifiedTKK
import InfoGeometry.Canonical.ZornTrialityTKKBridge

/-!
# Zorn triality defect bridge

The paper's coordinate-free triality expression uses a conjugation and a
trilinear form.  The current Lean repository does not yet have a full
conjugation algebra for the split-octonion carrier, so this file records the
finite defect bridge that is already available:

* the associator is the concrete trilinear defect witness;
* the canonical mixed upper/lower/upper triple is nonzero;
* the defect lane routes to `g_2` in the existing TKK bridge.

This is theorem-honest: it packages the defect triality lane now, while leaving
the explicit division-octonion conjugation form as future structure.
-/

noncomputable section

namespace ZornTrialityFormSocket

open ZornCore
open ZornAssociatorSplitOctonion
open GrandUnifiedTKK
open ZornTrialityTKKBridge
open TKKJordanPairData

/-- The finite trilinear defect bridge available in the current repository. -/
def trialityDefect (Φ X Ψ : ZornCore.Zorn) : ZornCore.Zorn :=
  associator Φ X Ψ

/-- The defect witness is definitionally the associator. -/
theorem trialityDefect_eq_associator (Φ X Ψ : ZornCore.Zorn) :
    trialityDefect Φ X Ψ = associator Φ X Ψ := by
  rfl

/-- The canonical triality defect witness is the mixed upper/lower/upper
associator already proved nonzero. -/
theorem canonical_trialityDefect_nonzero :
    trialityDefect (U e1) (L e1) (U e2) ≠ 0 := by
  simpa [trialityDefect_eq_associator] using mixed_nonassociative

/-- The canonical defect lane routes to the extremal TKK grade. -/
theorem canonical_trialityDefect_grade :
    laneGrade SplitOctonionLane.associatorWitness = TKKGrade.p2 := by
  exact laneGrade_associatorWitness

/-- The finite triality bridge summary used by the bridge layer. -/
theorem trialityDefect_socket_synthesis :
    trialityDefect (U e1) (L e1) (U e2) ≠ 0 ∧
    laneGrade SplitOctonionLane.associatorWitness = TKKGrade.p2 := by
  have hNonzero := canonical_trialityDefect_nonzero
  have hGrade := canonical_trialityDefect_grade
  exact ⟨hNonzero, hGrade⟩

end ZornTrialityFormSocket
