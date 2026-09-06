import InfoGeometry.Canonical.CountPositiveCoupling
import InfoGeometry.Canonical.SinkhornFoundation

namespace InfoGeometry.Canonical.CountSubstrateBridge

open InfoGeometry.Canonical.MoE

section CountInducedFlow

variable (n : Nat)
variable (N : CountSubstrate (Fin n))

noncomputable def countInducedSinkhornTrajectory : SinkhornTrajectory n :=
  { state := countInducedIterate (n := n) N
    step := countInducedIterate_step (n := n) N }

/-- Every state of the count-induced Sinkhorn trajectory is entrywise positive. -/
lemma countInducedSinkhornTrajectory_state_entrywisePositive (k : Nat) :
    EntrywisePositive n ((countInducedSinkhornTrajectory (n := n) N).state k) := by
  exact countInducedIterate_entrywisePositive (n := n) N k

/-- Every state of the count-induced Sinkhorn trajectory has positive row sums. -/
lemma countInducedSinkhornTrajectory_state_hasPositiveRowSums (k : Nat) :
    HasPositiveRowSums n ((countInducedSinkhornTrajectory (n := n) N).state k) := by
  exact countInducedIterate_hasPositiveRowSums (n := n) N k

/-- Every state of the count-induced Sinkhorn trajectory has positive column sums. -/
lemma countInducedSinkhornTrajectory_state_hasPositiveColSums (k : Nat) :
    HasPositiveColSums n ((countInducedSinkhornTrajectory (n := n) N).state k) := by
  exact countInducedIterate_hasPositiveColSums (n := n) N k

def CountInducedEmergentTimeFlow (T : SinkhornTrajectory n) : Prop :=
  ∀ k : Nat, trajectoryLyapunovNext n T k ≤ trajectoryLyapunov n T k

theorem emergentTimeFlow_countInducedSinkhornTrajectory :
    CountInducedEmergentTimeFlow n (countInducedSinkhornTrajectory (n := n) N) := by
  intro k
  exact trajectoryLyapunov_monotone (n := n) (countInducedSinkhornTrajectory (n := n) N) k

end CountInducedFlow

end InfoGeometry.Canonical.CountSubstrateBridge
