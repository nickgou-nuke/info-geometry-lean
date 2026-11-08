/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11StarAlgebraColimit
import InfoGeometry.Clifford.Cl11TensorTowerProjectionRank
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Monotone.Basic

/-!
# The strict full-matrix filtration of the real star-algebra colimit

The stage images are native star subalgebras of the existing direct limit.
Their inclusions form an actual order embedding, and their supremum is the
whole algebra. A fresh off-diagonal matrix entry proves strict growth at
each successor. Faithful stage maps and the dimensions `4 ^ n` establish
algebraic infinite dimensionality without a topological completion.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11StarAlgebraFiltration

open Cl11TensorTower Cl11TensorTowerLimit Cl11StarAlgebraColimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- Full matrix stages as native star subalgebras of the actual quotient. -/
def stageImage (n : ℕ) : StarSubalgebra ℝ Limit :=
  (ofStageStarAlgHom n).range

theorem mem_stageImage {n : ℕ} {x : Limit} :
    x ∈ stageImage n ↔ ∃ A : Stage n, ofStage n A = x := Iff.rfl

/-- Every iterated bonding map gives an inclusion of the corresponding images. -/
theorem stageImage_mono : Monotone stageImage := by
  intro m n h x hx
  obtain ⟨A, rfl⟩ := mem_stageImage.mp hx
  apply mem_stageImage.mpr
  exact ⟨bondMap stageBond m n h A, directLimitOf_bondMap stageBond m n h A⟩

/-- Every quotient element has a representative in an actual finite matrix stage. -/
theorem exists_stageImage (x : Limit) : ∃ n, x ∈ stageImage n := by
  induction x using DirectLimit.induction with
  | _ n A => exact ⟨n, mem_stageImage.mpr ⟨A, rfl⟩⟩

theorem iSup_stageImage_eq_top : (⨆ n, stageImage n) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n, hx⟩ := exists_stageImage x
  exact (le_iSup stageImage n) hx

/-- The new last-factor off-diagonal matrix unit cannot come from the preceding stage. -/
theorem stageImage_lt_succ (n : ℕ) : stageImage n < stageImage (n + 1) := by
  refine lt_of_le_of_ne (stageImage_mono (Nat.le_succ n)) ?_
  intro h
  let i : TowerMatrix.Idx n := default
  let B : Stage (n + 1) :=
    Matrix.single (i, (0 : Fin 2)) (i, (1 : Fin 2)) (1 : ℝ)
  have hB : ofStage (n + 1) B ∈ stageImage n := by
    rw [h]
    exact mem_stageImage.mpr ⟨B, rfl⟩
  obtain ⟨A, hA⟩ := mem_stageImage.mp hB
  have hAB : stageEmbed n A = B :=
    ofStage_injective (n + 1) ((ofStage_apply_bond n A).trans hA)
  have hentry : (0 : ℝ) = 1 := by
    calc
      0 = stageEmbed n A (i, (0 : Fin 2)) (i, (1 : Fin 2)) := by
        norm_num [stageEmbed_apply, matStageEmbed]
      _ = B (i, (0 : Fin 2)) (i, (1 : Fin 2)) :=
        congrArg (fun M : Stage (n + 1) => M (i, (0 : Fin 2)) (i, (1 : Fin 2))) hAB
      _ = 1 := Matrix.single_apply_same _ _ _
  exact zero_ne_one hentry

theorem stageImage_strictMono : StrictMono stageImage :=
  strictMono_nat_of_lt_succ stageImage_lt_succ

/-- The tower order is realized faithfully inside the native subalgebra partial order. -/
def stageImageOrderEmbedding : ℕ ↪o StarSubalgebra ℝ Limit :=
  OrderEmbedding.ofStrictMono stageImage stageImage_strictMono

/-- Any finite collection of limit operators lies in one common full matrix stage. -/
theorem exists_stageImage_finset (s : Finset Limit) :
    ∃ n, ∀ x ∈ s, x ∈ stageImage n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x s _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm⟩ := exists_stageImage x
    refine ⟨max m n, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact stageImage_mono (le_max_left m n) hm
    · exact stageImage_mono (le_max_right m n) (hn y hy)

/-- Faithfulness identifies the dimension of a stage image with the full matrix dimension. -/
theorem stageImage_finrank (n : ℕ) :
    Module.finrank ℝ (stageImage n) = 4 ^ n := by
  calc
    Module.finrank ℝ (stageImage n) = Module.finrank ℝ (Stage n) :=
      (StarAlgEquiv.ofInjective (ofStageStarAlgHom n)
        (ofStageStarAlgHom_injective n)).toAlgEquiv.toLinearEquiv.finrank_eq.symm
    _ = 4 ^ n := matStage_finrank n

/-- The faithful direct limit of the full real matrix tower is not finite-dimensional. -/
theorem not_moduleFinite : ¬ Module.Finite ℝ Limit := by
  intro h
  let := h
  let d := Module.finrank ℝ Limit
  have hdim : 4 ^ d ≤ d := by
    simpa only [matStage_finrank] using
      (LinearMap.finrank_le_finrank_of_injective
        (f := (ofStageStarAlgHom d).toAlgHom.toLinearMap)
        (ofStageStarAlgHom_injective d))
  exact (Nat.not_lt_of_ge hdim) (Nat.lt_pow_self (by decide : 1 < 4))

end InfoGeometry.Clifford.Cl11StarAlgebraFiltration
