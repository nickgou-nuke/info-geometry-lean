/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Canonical.IBContractionFixedPoint
import InfoGeometry.Canonical.YangBaxterProof

open scoped BigOperators ENNReal NNReal Topology

/-!
# IB Contraction Metric, Blahut-Arimoto Fixed Point & Information Equilibrium Capstone

Canonical umbrella export connecting the metric contraction of the Blahut-Arimoto operator,
Banach fixed-point existence and uniqueness of information equilibrium, geometric decay,
and topological Yang-Baxter integrability.
-/

namespace InfoGeometry.Canonical.IB

open InfoGeometry
open InfoGeometry.Canonical.YangBaxterProof

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

/-- 🏆 Canonical Grand Synthesis of IB Contraction, Information Equilibrium & Yang-Baxter Integrability -/
theorem grand_canonical_ib_contraction_information_equilibrium_synthesis
    [MetricSpace (X → FinProb T)]
    [CompleteSpace (X → FinProb T)]
    [Nonempty (X → FinProb T)]
    (prob : IBProblem (X := X) (Y := Y))
    (p0 : X → FinProb T)
    {Kc : ℝ≥0}
    (hK : Kc < 1)
    (hContr : ContractingWith Kc (ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob)) :
    (∃! p_star : X → FinProb T,
      ibBlahutArimotoStep (X := X) (Y := Y) (T := T) prob p_star = p_star) ∧
    (Filter.Tendsto (ibTrajectory prob p0) Filter.atTop
      (nhds (ContractingWith.fixedPoint (f := ibBlahutArimotoStep prob) (hf := hContr)))) ∧
    (CauchySeq (ibTrajectory prob p0)) ∧
    (∀ n : ℕ, dist (ibTrajectory prob p0 n)
         (ContractingWith.fixedPoint (f := ibBlahutArimotoStep prob) (hf := hContr)) ≤
      dist p0 (ibBlahutArimotoStep prob p0) * (Kc : ℝ) ^ n / (1 - (Kc : ℝ))) ∧
    (Filter.Tendsto (fun n : ℕ => (Kc : ℝ) ^ n * (1 / (1 - (Kc : ℝ)))) Filter.atTop (nhds 0)) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨ib_information_equilibrium_existence_and_uniqueness prob hContr,
   ib_trajectory_tendsto_information_equilibrium prob p0 hContr,
   ib_trajectory_is_cauchy prob p0 hContr,
   ib_parameter_error_bound prob p0 hContr,
   geom_decay_tendsto_zero hK 1,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.IB
