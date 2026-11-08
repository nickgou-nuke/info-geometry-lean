/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsModelFamily
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Joint responsibility volume and its marginals

Uniformly averaging responsibilities over observations produces a finite joint
distribution on model assignments and observations.  Its model marginal is
the model-volume vector, while its observation marginal is uniform.  This is
the finite coarse-graining identity behind the model-volume construction.
-/

namespace InfoGeometry.Inference.FiniteGibbs

open scoped BigOperators

variable {ModelId Data : Type*} [Fintype ModelId] [Nonempty ModelId]
  [Fintype Data] [Nonempty Data]

/-- Joint model-observation volume induced by uniform observation mass. -/
noncomputable def jointModelDataVolume
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (m : ModelId) (i : Data) : ℝ :=
  responsibility F ε m i / Fintype.card Data

theorem jointModelDataVolume_pos
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (m : ModelId) (i : Data) :
    0 < jointModelDataVolume F ε m i := by
  unfold jointModelDataVolume
  exact div_pos (responsibility_pos F ε m i) (by exact_mod_cast Fintype.card_pos)

/-- The model-volume vector is the model marginal of the joint volume. -/
theorem modelVolume_eq_sum_jointModelDataVolume
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (m : ModelId) :
    modelVolume F ε m = ∑ i : Data, jointModelDataVolume F ε m i := by
  unfold modelVolume jointModelDataVolume
  exact Finset.sum_div
    (s := (Finset.univ : Finset Data))
    (f := fun i : Data => responsibility F ε m i)
    (a := Fintype.card Data)

/-- Every observation has uniform mass in the joint volume marginal. -/
theorem jointModelDataVolume_sum_models
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (i : Data) :
    ∑ m : ModelId, jointModelDataVolume F ε m i =
      1 / Fintype.card Data := by
  unfold jointModelDataVolume
  calc
    ∑ m : ModelId, responsibility F ε m i / Fintype.card Data =
        (∑ m : ModelId, responsibility F ε m i) / Fintype.card Data := by
      exact (Finset.sum_div
        (s := (Finset.univ : Finset ModelId))
        (f := fun m : ModelId => responsibility F ε m i)
        (a := Fintype.card Data)).symm
    _ = 1 / Fintype.card Data := by rw [responsibilities_sum_one]

/-- The joint model-observation volume is normalized. -/
theorem jointModelDataVolume_sum_all
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) :
    ∑ m : ModelId, ∑ i : Data, jointModelDataVolume F ε m i = 1 := by
  calc
    ∑ m : ModelId, ∑ i : Data, jointModelDataVolume F ε m i =
        ∑ m : ModelId, modelVolume F ε m := by
      apply Finset.sum_congr rfl
      intro m hm
      exact (modelVolume_eq_sum_jointModelDataVolume F ε m).symm
    _ = 1 := modelVolumes_sum_one F ε

end InfoGeometry.Inference.FiniteGibbs
