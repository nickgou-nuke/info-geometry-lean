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

def CountInducedEmergentTimeFlow (T : SinkhornTrajectory n) : Prop :=
  ∀ k : Nat, trajectoryLyapunovNext n T k ≤ trajectoryLyapunov n T k

theorem emergentTimeFlow_countInducedSinkhornTrajectory :
    CountInducedEmergentTimeFlow n (countInducedSinkhornTrajectory (n := n) N) := by
  intro k
  exact trajectoryLyapunov_monotone (n := n) (countInducedSinkhornTrajectory (n := n) N) k

end CountInducedFlow

end InfoGeometry.Canonical.CountSubstrateBridge
