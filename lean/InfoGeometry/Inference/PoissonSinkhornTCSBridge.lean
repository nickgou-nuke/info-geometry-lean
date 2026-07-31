/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/

import InfoGeometry.Inference.TCSPoissonModel

/-!
# Poisson transport bridge for TCS mixtures

This module formalizes the finite contract shared by the Python transport
testbench and the TCS inference model.  A nonnegative Poisson-Bregman cost
matrix is converted into a row-normalized Gibbs assignment kernel.  The
kernel is an evidence assignment, not an outlier posterior and not a proof
that a numerical Sinkhorn iteration converges.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

section FinitePoissonTransport

variable {Observation Component : Type*}
  [Fintype Component] [Nonempty Component]

/-- A finite nonnegative cost matrix for observation/component assignments. -/
structure PoissonTransportCost where
  cost : Observation → Component → ℝ
  cost_nonneg : ∀ i j, 0 ≤ cost i j

/-- The row Gibbs assignment induced by a Poisson transport cost. -/
noncomputable def poissonTransportAssignment
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (ε : ℝ)
    (i : Observation) (j : Component) : ℝ :=
  Real.exp (-C.cost i j / ε) /
    ∑ k : Component, Real.exp (-C.cost i k / ε)

theorem poissonTransportAssignment_pos
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (ε : ℝ)
    (i : Observation) (j : Component) :
    0 < poissonTransportAssignment C ε i j := by
  unfold poissonTransportAssignment
  exact div_pos (Real.exp_pos _)
    (Finset.sum_pos (fun k _ => Real.exp_pos _)
      Finset.univ_nonempty)

theorem poissonTransportAssignment_nonneg
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (ε : ℝ)
    (i : Observation) (j : Component) :
    0 ≤ poissonTransportAssignment C ε i j :=
  (poissonTransportAssignment_pos C ε i j).le

/-- Every observation distributes unit mass across the candidate components. -/
theorem poissonTransportAssignment_row_sum_one
    (C : PoissonTransportCost (Observation := Observation)
      (Component := Component)) (ε : ℝ) (i : Observation) :
    ∑ j : Component, poissonTransportAssignment C ε i j = 1 := by
  classical
  unfold poissonTransportAssignment
  have hZ : (∑ k : Component, Real.exp (-C.cost i k / ε)) ≠ 0 := by
    exact (Finset.sum_pos (fun k _ => Real.exp_pos _)
      Finset.univ_nonempty).ne'
  calc
    ∑ j : Component,
        Real.exp (-C.cost i j / ε) /
          ∑ k : Component, Real.exp (-C.cost i k / ε)
        = (∑ j : Component, Real.exp (-C.cost i j / ε)) /
            ∑ k : Component, Real.exp (-C.cost i k / ε) := by
              simp_rw [div_eq_mul_inv]
              rw [Finset.sum_mul]
    _ = 1 := by
      exact div_self hZ

/-- Poisson-Bregman costs form an admissible transport-cost matrix. -/
noncomputable def tcsPoissonTransportCost
    {x liveTime observed : Observation → ℝ}
    (hobs : ∀ i, 0 ≤ observed i)
    (components : Component → TCSParameter x liveTime) :
    PoissonTransportCost (Observation := Observation)
      (Component := Component) where
  cost := fun i j =>
    poissonBregman (observed i)
      (tcsMean (components j) i)
  cost_nonneg := by
    intro i j
    exact poissonBregman_nonneg (hobs i)
      ((components j).mean_pos i)

theorem tcsPoissonTransportAssignment_row_sum_one
    {x liveTime observed : Observation → ℝ}
    (hobs : ∀ i, 0 ≤ observed i)
    (components : Component → TCSParameter x liveTime)
    (ε : ℝ) (i : Observation) :
    ∑ j : Component,
      poissonTransportAssignment
        (tcsPoissonTransportCost hobs components) ε i j = 1 :=
  poissonTransportAssignment_row_sum_one
    (tcsPoissonTransportCost hobs components) ε i

end FinitePoissonTransport

end InfoGeometry.Inference
