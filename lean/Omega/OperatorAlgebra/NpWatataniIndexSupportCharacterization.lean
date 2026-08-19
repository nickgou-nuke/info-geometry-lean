import Mathlib.Data.Fintype.Card
import Omega.OperatorAlgebra.FoldWatataniIndexMultiplicityField

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {X W : Type*} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]

/-- Accepted input-candidate pairs for the verifier `V`. -/
abbrev verifierAcceptedPairs (V : X → W → Bool) :=
  { p : X × W // V p.1 p.2 = true }

/-- The verifier fold forgets the candidate and keeps the input. -/
def verifierFold (V : X → W → Bool) : verifierAcceptedPairs V → X :=
  fun p => p.1.1

/-- Candidates accepted by `V` for the fixed input `x`. -/
abbrev verifierCandidates (V : X → W → Bool) (x : X) :=
  { w : W // V x w = true }

/-- The accepted-candidate count for `x`. -/
def verifierCandidateCount (V : X → W → Bool) (x : X) : ℕ :=
  Fintype.card (verifierCandidates V x)

/-- The projector indexed by `x` lies in the Watatani-index support exactly when its coefficient
is positive. -/
def verifierProjectorInSupport (V : X → W → Bool) (x : X) : Prop :=
  0 < foldWatataniIndexElement (verifierFold V) x

private def verifierFiberEquivCandidates (V : X → W → Bool) (x : X) :
    foldFiber (verifierFold V) x ≃ verifierCandidates V x where
  toFun p := by
    rcases p with ⟨⟨⟨x', w⟩, hw⟩, hx⟩
    exact ⟨w, by simpa [verifierFold] using hx ▸ hw⟩
  invFun w := ⟨⟨(x, w.1), w.2⟩, rfl⟩
  left_inv p := by
    rcases p with ⟨⟨⟨x', w⟩, hw⟩, hx⟩
    cases hx
    rfl
  right_inv w := by
    rcases w with ⟨w, hw⟩
    rfl

private theorem verifierFoldFiberCard_eq_candidateCount (V : X → W → Bool) (x : X) :
    Fintype.card (foldFiber (verifierFold V) x) = verifierCandidateCount V x := by
  exact Fintype.card_congr (verifierFiberEquivCandidates V x)

/-- Paper label: `thm:np-watatani-index-support-characterization`.
For the verifier fold on accepted `(input, witness)` pairs, the Watatani-index coefficient at `x`
is the witness count for `x`, so the projector support condition is exactly witness nonemptiness. -/
theorem paper_np_watatani_index_support_characterization (V : X → W → Bool) :
    (∀ x, foldWatataniIndexElement (verifierFold V) x = verifierCandidateCount V x) ∧
      ∀ x, verifierProjectorInSupport V x ↔ ∃ w, V x w = true := by
  have hcoeff : ∀ x, foldWatataniIndexElement (verifierFold V) x = verifierCandidateCount V x := by
    intro x
    have hIndex :=
      paper_op_algebra_fold_watatani_index_equals_multiplicity_field (verifierFold V)
    calc
      foldWatataniIndexElement (verifierFold V) x =
          Fintype.card (foldFiber (verifierFold V) x) := by
            exact hIndex.2.2 x
      _ = verifierCandidateCount V x := verifierFoldFiberCard_eq_candidateCount V x
  refine ⟨?_, ?_⟩
  · exact hcoeff
  · intro x
    constructor
    · intro hx
      have hcount : 0 < verifierCandidateCount V x := by
        simpa [verifierProjectorInSupport, hcoeff x] using hx
      rcases Fintype.card_pos_iff.mp (by simpa [verifierCandidateCount] using hcount) with ⟨w⟩
      exact ⟨w.1, w.2⟩
    · rintro ⟨w, hw⟩
      have hcount : 0 < verifierCandidateCount V x := by
        simpa [verifierCandidateCount] using
          (Fintype.card_pos_iff.mpr ⟨(⟨w, hw⟩ : verifierCandidates V x)⟩)
      simpa [verifierProjectorInSupport, hcoeff x] using hcount

end

end Omega.OperatorAlgebra
