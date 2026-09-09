import InfoGeometry.SignedNetwork.BranchingInitialization
import InfoGeometry.SignedNetwork.BranchingEventLaw
import InfoGeometry.SignedNetwork.BranchingEnsembleGenerator
import InfoGeometry.SignedNetwork.BranchingQubitGenerator

/-! Verified finite boundary of the signed-network branching reconstruction.
The continuous-time process remains a separate development frontier. -/
namespace InfoGeometry.SignedNetwork.BranchingFrontier

open InfoGeometry.SignedNetwork.BranchingEnsembleGenerator
open InfoGeometry.SignedNetwork.BranchingEventLaw

variable {C : Type*} [Fintype C] [DecidableEq C]

/-! The finite event law has a genuine conservation statement: an event adds
one positive target and one negative source, so its total signed readout is
unchanged.  This is deliberately a finite algebraic result; it is not a
claim about a continuous-time branching process. -/
theorem total_signedReal_applyEvent (p : ExactCancellation.Counts C)
    (e : BranchingEventLaw.Event C) :
    (∑ x, signedReal (BranchingEnsembleGenerator.applyEvent p e) x) =
      ∑ x, signedReal p x := by
  calc
    (∑ x, signedReal (BranchingEnsembleGenerator.applyEvent p e) x) =
        ∑ x, (signedReal p x +
          ((if x = e.2 then (1 : ℝ) else 0) -
            (if x = e.1 then (1 : ℝ) else 0))) := by
      apply Finset.sum_congr rfl
      intro x hx
      have h := BranchingEnsembleGenerator.applyEvent_signed p e x
      linarith
    _ = ∑ x, signedReal p x := by
      rw [Finset.sum_add_distrib]
      have htarget : (∑ x : C, (if x = e.2 then (1 : ℝ) else 0)) = 1 := by
        simp
      have hsource : (∑ x : C, (if x = e.1 then (1 : ℝ) else 0)) = 1 := by
        simp
      rw [Finset.sum_sub_distrib, htarget, hsource]
      ring

end InfoGeometry.SignedNetwork.BranchingFrontier
