/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Finite Gibbs model-family decomposition

Observations may be assigned to a finite family of physical explanatory
models. Responsibilities are Gibbs probabilities over models for each datum;
they are not intrinsic outlier labels.
-/

open scoped BigOperators

namespace InfoGeometry.Inference.FiniteGibbs

variable {ModelId Data : Type*} [Fintype ModelId] [Nonempty ModelId]
  [Fintype Data] [Nonempty Data]

structure ModelFamily where
  energy : ModelId → Data → ℝ
  prior : ModelId → ℝ
  prior_pos : ∀ m, 0 < prior m

noncomputable def modelPartition
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (i : Data) : ℝ :=
  ∑ m : ModelId, F.prior m * Real.exp (-F.energy m i / ε)

noncomputable def responsibility
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (m : ModelId) (i : Data) : ℝ :=
  (F.prior m * Real.exp (-F.energy m i / ε)) /
    modelPartition F ε i

theorem modelPartition_pos
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (i : Data) :
    0 < modelPartition F ε i := by
  unfold modelPartition
  exact Finset.sum_pos
    (fun m hm => mul_pos (F.prior_pos m) (Real.exp_pos _))
    Finset.univ_nonempty

theorem responsibility_pos
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (m : ModelId) (i : Data) :
    0 < responsibility F ε m i := by
  unfold responsibility
  exact div_pos (mul_pos (F.prior_pos m) (Real.exp_pos _))
    (modelPartition_pos F ε i)

theorem responsibility_nonneg
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (m : ModelId) (i : Data) :
    0 ≤ responsibility F ε m i :=
  (responsibility_pos F ε m i).le

theorem responsibilities_sum_one
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (i : Data) :
    ∑ m : ModelId, responsibility F ε m i = 1 := by
  unfold responsibility
  have hZ : modelPartition F ε i ≠ 0 :=
    (modelPartition_pos F ε i).ne'
  calc
    ∑ m : ModelId,
        (F.prior m * Real.exp (-F.energy m i / ε)) /
          modelPartition F ε i =
      (∑ m : ModelId, F.prior m * Real.exp (-F.energy m i / ε)) /
        modelPartition F ε i := by
          symm
          exact Finset.sum_div
            (s := (Finset.univ : Finset ModelId))
            (f := fun m : ModelId =>
              F.prior m * Real.exp (-F.energy m i / ε))
            (a := modelPartition F ε i)
    _ = 1 := by
      rw [show (∑ m : ModelId,
        F.prior m * Real.exp (-F.energy m i / ε)) =
          modelPartition F ε i by rfl]
      exact div_self hZ

noncomputable def modelVolume
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (m : ModelId) : ℝ :=
  (∑ i : Data, responsibility F ε m i) / Fintype.card Data

theorem modelVolume_pos
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (m : ModelId) :
    0 < modelVolume F ε m := by
  unfold modelVolume
  apply div_pos
  · exact Finset.sum_pos (fun i hi => responsibility_pos F ε m i)
      Finset.univ_nonempty
  · exact_mod_cast Fintype.card_pos

theorem modelVolume_le_one
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (m : ModelId) :
    modelVolume F ε m ≤ 1 := by
  unfold modelVolume
  apply (div_le_iff₀
    (show (0 : ℝ) < Fintype.card Data by exact_mod_cast Fintype.card_pos)).2
  calc
    ∑ i : Data, responsibility F ε m i ≤ ∑ _i : Data, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun i hi => by
        have hsum := responsibilities_sum_one F ε i
        have hnonneg : ∀ n : ModelId, 0 ≤ responsibility F ε n i :=
          fun n => responsibility_nonneg F ε n i
        have hle : responsibility F ε m i ≤
            ∑ n : ModelId, responsibility F ε n i := by
          exact Finset.single_le_sum (fun n _hn => hnonneg n)
            (Finset.mem_univ m)
        simpa [hsum] using hle)
    _ = 1 * Fintype.card Data := by simp

end InfoGeometry.Inference.FiniteGibbs
