import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Convex.Bregman

namespace InfoGeometry.Topology.BregmanDivergence

/-- A topological Bregman readout is the same one-dimensional Bregman divergence
used by the convex core, viewed at the topology umbrella level. -/
noncomputable def topologicalBregmanDiv (F : ℝ → ℝ) (x y : ℝ) : ℝ :=
  InfoGeometry.bregmanDiv F x y

/-- The topological Bregman divergence vanishes on the diagonal. -/
theorem topologicalBregmanDiv_self (F : ℝ → ℝ) (x : ℝ) :
    topologicalBregmanDiv F x x = 0 := by
  simpa [topologicalBregmanDiv] using InfoGeometry.bregmanDiv_self F x

/-- The topological Bregman divergence obeys the same three-point identity. -/
theorem topologicalBregmanDiv_threePoint_eq_of_deriv_eq
    (F : ℝ → ℝ) (x y z : ℝ)
    (hderiv : deriv F y = deriv F z) :
    topologicalBregmanDiv F x z =
      topologicalBregmanDiv F x y + topologicalBregmanDiv F y z := by
  simpa [topologicalBregmanDiv] using
    InfoGeometry.bregmanThreePoint_eq_of_deriv_eq F x y z hderiv

end InfoGeometry.Topology.BregmanDivergence
