/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FiniteRealFockMetric
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

/-!
# All-index isometries of the native real Fock tower

The existing iterated zero-head maps preserve the accepted finite real Fock
metric. Their identity and composition laws are inherited from the native
algebraic transitions. No new carrier or completion is constructed here.
-/
noncomputable section

namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

/-- Every actual iterated tail inclusion preserves the real Fock inner product. -/
theorem fockStageMap_inner (m n : ℕ) (h : m ≤ n) (x y : FockStage m) :
    inner ℝ (fockStageMap m n h x) (fockStageMap m n h y) = inner ℝ x y := by
  induction n, h using Nat.le_induction with
  | base => simp only [fockStageMap_refl, LinearMap.id_apply]
  | succ n h ih =>
      rw [fockStageMap_succ (m := m) (n := n) h]
      change inner ℝ (fockTailMap n (fockStageMap m n h x))
        (fockTailMap n (fockStageMap m n h y)) = inner ℝ x y
      exact (fockTailMap_inner n _ _).trans ih

/-- The same native transition, bundled with its derived metric preservation. -/
def fockStageLinearIsometry (m n : ℕ) (h : m ≤ n) :
    FockStage m →ₗᵢ[ℝ] FockStage n :=
  (fockStageMap m n h).isometryOfInner (fockStageMap_inner m n h)

@[simp] theorem fockStageLinearIsometry_apply (m n : ℕ) (h : m ≤ n)
    (x : FockStage m) :
    fockStageLinearIsometry m n h x = fockStageMap m n h x := rfl

/-- Norm preservation follows from the positive metric, not the zero quadratic form. -/
theorem fockStageMap_norm (m n : ℕ) (h : m ≤ n) (x : FockStage m) :
    ‖fockStageMap m n h x‖ = ‖x‖ :=
  (fockStageLinearIsometry m n h).norm_map x

/-- Identity coherence for the actual metric transition maps. -/
theorem fockStageLinearIsometry_refl (m : ℕ) :
    fockStageLinearIsometry m m le_rfl = LinearIsometry.id := by
  ext x
  change fockStageMap m m le_rfl x = x
  rw [fockStageMap_refl, LinearMap.id_apply]

/-- Composition coherence is inherited from the existing all-index Fock maps. -/
theorem fockStageLinearIsometry_comp (m n k : ℕ) (hmn : m ≤ n) (hnk : n ≤ k) :
    (fockStageLinearIsometry n k hnk).comp (fockStageLinearIsometry m n hmn) =
      fockStageLinearIsometry m k (hmn.trans hnk) := by
  ext x
  change fockStageMap n k hnk (fockStageMap m n hmn x) =
    fockStageMap m k (hmn.trans hnk) x
  exact (fockStageMap_apply_trans m n k hmn hnk x).symm

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
