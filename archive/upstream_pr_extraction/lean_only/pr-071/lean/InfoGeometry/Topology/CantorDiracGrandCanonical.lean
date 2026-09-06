import Mathlib.Tactic
import InfoGeometry.Core.GrandCanonical
import InfoGeometry.Topology.CantorDiracOperator

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Topology.CantorDiracGrandCanonical

open InfoGeometry.Topology.CantorDiracOperator

def occupancy {n : ℕ}
    (w : (Fin n → Bool)) : ℝ :=
  ∑ i : Fin n, if w i then 1 else 0

def params
    (cutoff : ℕ)
    (scale : ℕ → ℝ) :
    InfoGeometry.GrandCanonical.GrandCanonicalTwoParam
      ((Fin cutoff → Bool)) where
  energy := fun w => scale cutoff * occupancy w
  number := occupancy

theorem occupancy_nonnegative
    {cutoff : ℕ}
    (w : (Fin cutoff → Bool)) :
    0 ≤ occupancy w := by
  dsimp [occupancy]
  exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)

theorem partition_pos
    (cutoff : ℕ) (scale : ℕ → ℝ) (β μ : ℝ) :
    0 < InfoGeometry.Core.partitionGC (params cutoff scale) β μ := by
  exact InfoGeometry.Core.gc2_partition_pos (params cutoff scale) β μ

theorem gibbsWeight_nonnegative
    (cutoff : ℕ) (scale : ℕ → ℝ) (β μ : ℝ)
    (w : (Fin cutoff → Bool)) :
    0 ≤ InfoGeometry.Core.gibbsWeightGC (params cutoff scale) β μ w := by
  exact InfoGeometry.Core.gc2_gibbsWeight_nonneg (params cutoff scale) β μ w

theorem gibbsWeight_sum_one
    (cutoff : ℕ) (scale : ℕ → ℝ) (β μ : ℝ) :
    ∑ w : (Fin cutoff → Bool),
      InfoGeometry.Core.gibbsWeightGC (params cutoff scale) β μ w = 1 := by
  exact InfoGeometry.Core.gc2_gibbsWeight_sum_one (params cutoff scale) β μ

theorem betaResponse_eq_neg_meanShift
    (cutoff : ℕ) (scale : ℕ → ℝ) (β μ : ℝ) :
    InfoGeometry.Core.GrandCanonical.TwoParam.betaResponse
        (params cutoff scale) β μ =
      -InfoGeometry.Core.meanShift (params cutoff scale) β μ := by
  exact InfoGeometry.Core.GrandCanonical.TwoParam.gc2_betaResponse_eq_neg_meanShift
    (params cutoff scale) β μ

theorem muResponse_eq_beta_meanNumber
    (cutoff : ℕ) (scale : ℕ → ℝ) (β μ : ℝ) :
    InfoGeometry.Core.GrandCanonical.TwoParam.muResponse
        (params cutoff scale) β μ =
      β * InfoGeometry.Core.meanNumber (params cutoff scale) β μ := by
  exact InfoGeometry.Core.GrandCanonical.TwoParam.gc2_muResponse_eq_beta_meanNumber
    (params cutoff scale) β μ

end InfoGeometry.Topology.CantorDiracGrandCanonical
