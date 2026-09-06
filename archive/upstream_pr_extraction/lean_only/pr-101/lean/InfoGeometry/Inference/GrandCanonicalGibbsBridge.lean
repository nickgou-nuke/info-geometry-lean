/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Inference.FiniteGibbsInference

/-!
# Grand-canonical bridge to the finite Gibbs kernel

For positive inverse temperature, the existing grand-canonical weights are the
finite Gibbs weights at temperature `ε = 1 / β` for the shifted energy
`E - μ N`. This is an exact finite identity, not a thermodynamic-limit claim.
-/

namespace InfoGeometry.GrandCanonical

open InfoGeometry.Inference
open InfoGeometry.Inference.FiniteGibbs
open scoped BigOperators

variable {α : Type*} [Fintype α] [Nonempty α]

noncomputable def finiteGibbsModel
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) (μ : ℝ) :
    FiniteGibbs.Model (Data := α) (Theta := Unit) :=
  fun x _ => shiftedEnergy params μ x

theorem partitionGC_eq_finiteGibbs_partition
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) {β μ : ℝ} (hβ : 0 < β) :
    partitionGC params β μ =
      partitionFunction (finiteGibbsModel params μ) () (1 / β) := by
  unfold partitionGC partitionFunction finiteGibbsModel
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  field_simp [ne_of_gt hβ]

theorem gibbsWeightGC_eq_finiteGibbs_weight
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α) {β μ : ℝ} (hβ : 0 < β) (x : α) :
    gibbsWeightGC params β μ x =
      weight (finiteGibbsModel params μ) () (1 / β) x := by
  unfold gibbsWeightGC weight finiteGibbsModel
  rw [partitionGC_eq_finiteGibbs_partition params hβ]
  congr 1
  field_simp [ne_of_gt hβ]

end InfoGeometry.GrandCanonical
