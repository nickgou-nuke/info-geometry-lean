import Mathlib.Tactic
import InfoGeometry.Core.GrandCanonical
import InfoGeometry.Topology.CantorDiracOperator

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Topology.CantorDiracGrandCanonical

open InfoGeometry.Topology.CantorDiracOperator

abbrev CantorState (n : ℕ) :=
  InfoGeometry.Topology.CliffordFractalWaveletBridge.BinaryWord n

instance (n : ℕ) : Fintype (CantorState n) := by
  dsimp [CantorState]
  infer_instance

instance (n : ℕ) : Nonempty (CantorState n) := by
  dsimp [CantorState]
  infer_instance

def occupancy {n : ℕ} (w : CantorState n) : ℝ :=
  ∑ i : Fin n, if w i then 1 else 0

def params
    (cutoff : ℕ)
    (scale : CantorDiracScale) :
    InfoGeometry.GrandCanonical.GrandCanonicalTwoParam (CantorState cutoff) where
  energy := fun w => scale cutoff * occupancy w
  number := occupancy

def partition (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.partitionGC (params cutoff scale) β μ

def potential (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.potentialGC (params cutoff scale) β μ

def gibbsWeight
    (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ)
    (w : CantorState cutoff) : ℝ :=
  InfoGeometry.GrandCanonical.gibbsWeightGC (params cutoff scale) β μ w

def meanShift (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.meanShift (params cutoff scale) β μ

def meanNumber (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.meanNumber (params cutoff scale) β μ

def betaResponse (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaResponse (params cutoff scale) β μ

def muResponse (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muResponse (params cutoff scale) β μ

def betaHessian (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaHessian (params cutoff scale) β μ

def muHessian (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muHessian (params cutoff scale) β μ

def betaMuHessian (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.betaMuHessian (params cutoff scale) β μ

def muBetaHessian (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.muBetaHessian (params cutoff scale) β μ

def responseMatrix (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) :
    InfoGeometry.GrandCanonical.ResponseMatrix2 :=
  InfoGeometry.GrandCanonical.responseMatrix (params cutoff scale) β μ

def spinodal2D (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) : Prop :=
  InfoGeometry.GrandCanonical.Spinodal2D (params cutoff scale) β μ

theorem occupancy_nonnegative
    {cutoff : ℕ} (w : CantorState cutoff) :
    0 ≤ occupancy w := by
  dsimp [occupancy]
  exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)

theorem partition_pos
    (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) :
    0 < partition cutoff scale β μ := by
  exact InfoGeometry.Core.gc2_partition_pos (params cutoff scale) β μ

theorem gibbsWeight_nonnegative
    (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ)
    (w : CantorState cutoff) :
    0 ≤ gibbsWeight cutoff scale β μ w := by
  exact InfoGeometry.Core.gc2_gibbsWeight_nonneg (params cutoff scale) β μ w

theorem gibbsWeight_sum_one
    (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) :
    ∑ w : CantorState cutoff, gibbsWeight cutoff scale β μ w = 1 := by
  exact InfoGeometry.Core.gc2_gibbsWeight_sum_one (params cutoff scale) β μ

theorem betaResponse_eq_neg_meanShift
    (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) :
    betaResponse cutoff scale β μ = -meanShift cutoff scale β μ := by
  exact InfoGeometry.Core.GrandCanonical.TwoParam.gc2_betaResponse_eq_neg_meanShift
    (params cutoff scale) β μ

theorem muResponse_eq_beta_meanNumber
    (cutoff : ℕ) (scale : CantorDiracScale) (β μ : ℝ) :
    muResponse cutoff scale β μ = β * meanNumber cutoff scale β μ := by
  exact InfoGeometry.Core.GrandCanonical.TwoParam.gc2_muResponse_eq_beta_meanNumber
    (params cutoff scale) β μ

end InfoGeometry.Topology.CantorDiracGrandCanonical
