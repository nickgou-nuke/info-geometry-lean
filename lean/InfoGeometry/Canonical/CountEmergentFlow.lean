import InfoGeometry.Canonical.CountPositiveCoupling
import InfoGeometry.Canonical.HolographicEmergence

namespace InfoGeometry.Canonical.CountSubstrateBridge

open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.HolographicEmergence

section CountInducedFlow

variable (n : Nat)
variable (N : CountSubstrate (Fin n))

/-- Constructive Sinkhorn trajectory from the count-induced coupling. -/
noncomputable def countInducedSinkhornTrajectory : SinkhornTrajectory n :=
  { state := countInducedIterate (n := n) N
    step := countInducedIterate_step (n := n) N }

/-- Count-induced Sinkhorn trajectories satisfy the emergent time-flow law. -/
theorem emergentTimeFlow_countInducedSinkhornTrajectory :
    EmergentTimeFlow n (countInducedSinkhornTrajectory (n := n) N) := by
  exact emergentTimeFlow_of_sinkhornTrajectory (n := n)
    (countInducedSinkhornTrajectory (n := n) N)

end CountInducedFlow

end InfoGeometry.Canonical.CountSubstrateBridge
