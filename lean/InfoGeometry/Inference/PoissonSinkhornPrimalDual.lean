/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/

import InfoGeometry.Inference.PoissonSinkhornTCSBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.GibbsUniqueMinimizer

/-!
# Row-wise primal-dual property for Poisson transport

The row Gibbs assignment is not merely a normalized heuristic: at positive
temperature it is the unique minimizer of the finite entropy-regularized
energy functional for that row.  Column constraints require the separate
Sinkhorn dual layer and are intentionally not asserted here.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Observation Component : Type*}
  [Fintype Component] [Nonempty Component]

/-- The finite Gibbs model represented by one row of a transport cost matrix. -/
noncomputable def poissonTransportRowModel
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component))
    (i : Observation) :
    FiniteGibbs.Model (Data := Component) (Theta := Unit) :=
  { energy := fun j _ => C.cost i j }

omit [Nonempty Component] in
theorem poissonTransportRowModel_weight_eq_assignment
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component))
    (ε : ℝ) (i : Observation) (j : Component) :
    FiniteGibbs.weight (poissonTransportRowModel C i) () ε j =
      poissonTransportAssignment C ε i j := by
  unfold FiniteGibbs.weight FiniteGibbs.partitionFunction
  rfl

theorem poissonTransportAssignment_unique_entropy_minimizer
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component))
    (ε : ℝ) (hε : 0 < ε) (i : Observation)
    (q : Component → ℝ)
    (hq_pos : ∀ j, 0 < q j)
    (hq_sum : ∑ j : Component, q j = 1) :
    FiniteGibbs.entropyRegularizedObjective
        (poissonTransportRowModel C i) () ε q =
        FiniteGibbs.freeEnergy (poissonTransportRowModel C i) () ε ↔
      q = poissonTransportAssignment C ε i := by
  simpa [poissonTransportRowModel, poissonTransportAssignment] using
    (FiniteGibbs.entropyRegularizedObjective_eq_freeEnergy_iff
      (poissonTransportRowModel C i) () hε q hq_pos hq_sum)

theorem poissonTransportRow_primalDual_gap_nonneg
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component))
    (ε : ℝ) (hε : 0 < ε) (i : Observation)
    (q : Component → ℝ)
    (hq_pos : ∀ j, 0 < q j)
    (hq_sum : ∑ j : Component, q j = 1) :
    FiniteGibbs.freeEnergy (poissonTransportRowModel C i) () ε ≤
      FiniteGibbs.entropyRegularizedObjective
        (poissonTransportRowModel C i) () ε q :=
  FiniteGibbs.entropyRegularizedObjective_ge_freeEnergy
    (poissonTransportRowModel C i) () hε q hq_pos hq_sum

end InfoGeometry.Inference
