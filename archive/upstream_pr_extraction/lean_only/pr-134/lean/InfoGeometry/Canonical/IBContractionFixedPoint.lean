/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import InfoGeometry.Canonical.IBTrajectory

namespace InfoGeometry.Canonical.IB

open scoped BigOperators ENNReal NNReal Topology
open InfoGeometry

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

/-!
# IB Contraction Metric, Blahut-Arimoto Fixed Point, and Information Equilibrium

We formalize:
1. Geometric contraction bound ensuring exponential decay of iteration defect.
2. Uniqueness and existence of the Blahut-Arimoto fixed point via the Banach contraction theorem.
3. Asymptotic convergence of arbitrary initial encoder trajectories `p0` to the unique Information Equilibrium state `p*`.
-/

/-- Geometric contraction bound: K^n / (1 - K) * d(p0, p1) tends to 0 as n → ∞. -/
theorem geom_decay_tendsto_zero {K : ℝ≥0} (hK : K < 1) (d0 : ℝ) :
    Filter.Tendsto (fun n : ℕ => (K : ℝ) ^ n * (d0 / (1 - (K : ℝ)))) Filter.atTop (nhds 0) := by
  have hK_nonneg : 0 ≤ (K : ℝ) := K.2
  have hK_lt : (K : ℝ) < 1 := hK
  have h_geom := tendsto_pow_atTop_nhds_zero_of_lt_one hK_nonneg hK_lt
  have h_mul := Filter.Tendsto.mul_const (d0 / (1 - (K : ℝ))) h_geom
  rw [zero_mul] at h_mul
  exact h_mul

/-- 🏆 THEOREM: Banach fixed-point existence and uniqueness of the Information Equilibrium encoder. -/
theorem ib_information_equilibrium_existence_and_uniqueness
    [m : MetricSpace (X → FinProb T)]
    [CompleteSpace (X → FinProb T)]
    [Nonempty (X → FinProb T)]
    (prob : IBProblem (X := X) (Y := Y))
    {Kc : ℝ≥0}
    (hContr : ContractingWith Kc (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)) :
    ∃! p_star : X → FinProb T,
      ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p_star = p_star := by
  let F := ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob
  use ContractingWith.fixedPoint (f := F) (hf := hContr)
  constructor
  · exact ContractingWith.fixedPoint_isFixedPt (f := F) (hf := hContr)
  · intro q hq
    exact ContractingWith.fixedPoint_unique (f := F) (hf := hContr) hq

/-- 🏆 THEOREM: Global iterate convergence from any initial encoder p0 to the equilibrium state p*. -/
theorem ib_trajectory_tendsto_information_equilibrium
    [m : MetricSpace (X → FinProb T)]
    [CompleteSpace (X → FinProb T)]
    [Nonempty (X → FinProb T)]
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T)
    {Kc : ℝ≥0}
    (hContr : ContractingWith Kc (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)) :
    Filter.Tendsto (ibTrajectory prob p0) Filter.atTop
      (nhds (ContractingWith.fixedPoint (f := ibBlahutArimotoStep prob) (hf := hContr))) := by
  have h_iter : ibTrajectory prob p0 = fun n => (ibBlahutArimotoStep prob)^[n] p0 := by
    funext n
    exact ibTrajectory_eq_iterate prob p0 n
  rw [h_iter]
  exact ContractingWith.tendsto_iterate_fixedPoint (f := ibBlahutArimotoStep prob) (hf := hContr) p0

/-- 🏆 THEOREM: The IB trajectory forms a Cauchy sequence in the parameter space under contraction. -/
theorem ib_trajectory_is_cauchy
    [m : MetricSpace (X → FinProb T)]
    [CompleteSpace (X → FinProb T)]
    [Nonempty (X → FinProb T)]
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T)
    {Kc : ℝ≥0}
    (hContr : ContractingWith Kc (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)) :
    CauchySeq (ibTrajectory prob p0) := by
  have htend := ContractingWith.tendsto_iterate_fixedPoint (f := ibBlahutArimotoStep prob) (hf := hContr) p0
  have h_iter : ibTrajectory prob p0 = fun n => (ibBlahutArimotoStep prob)^[n] p0 := by
    funext n
    exact ibTrajectory_eq_iterate prob p0 n
  rw [h_iter]
  exact htend.cauchySeq

/-- 🏆 THEOREM: Exponential reduction of error in parameter space to the thermodynamic equilibrium state. -/
theorem ib_parameter_error_bound
    [m : MetricSpace (X → FinProb T)]
    [CompleteSpace (X → FinProb T)]
    [Nonempty (X → FinProb T)]
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T)
    {Kc : ℝ≥0}
    (hContr : ContractingWith Kc (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob))
    (n : ℕ) :
    dist (ibTrajectory prob p0 n)
         (ContractingWith.fixedPoint (f := ibBlahutArimotoStep prob) (hf := hContr)) ≤
      dist p0 (ibBlahutArimotoStep prob p0) * (Kc : ℝ) ^ n / (1 - (Kc : ℝ)) := by
  have h_iter : ibTrajectory prob p0 n = (ibBlahutArimotoStep prob)^[n] p0 :=
    ibTrajectory_eq_iterate prob p0 n
  rw [h_iter]
  exact ContractingWith.apriori_dist_iterate_fixedPoint_le (f := ibBlahutArimotoStep prob) (hf := hContr) p0 n

end InfoGeometry.Canonical.IB
