/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsModelFamily
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Entropy effective volume of the model simplex

The model-volume distribution has an entropy-derived effective volume. This is
assignment-space volume, distinct from Fisher volume in parameter space.
-/

namespace InfoGeometry.Inference.FiniteGibbs

open scoped BigOperators

variable {ModelId Data : Type*} [Fintype ModelId] [Nonempty ModelId]
  [Fintype Data] [Nonempty Data]

noncomputable def modelVolumeEntropy
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) : ℝ :=
  -∑ m : ModelId,
      modelVolume F ε m * Real.log (modelVolume F ε m)

noncomputable def effectiveModelVolume
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) : ℝ :=
  Real.exp (modelVolumeEntropy F ε)

theorem modelVolumeEntropy_term_nonneg
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (m : ModelId) :
    0 ≤ -(modelVolume F ε m * Real.log (modelVolume F ε m)) := by
  apply neg_nonneg.mpr
  exact mul_nonpos_of_nonneg_of_nonpos (modelVolume_pos F ε m).le
    (Real.log_nonpos (modelVolume_pos F ε m).le
      (modelVolume_le_one F ε m))

theorem modelVolumeEntropy_nonneg
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) :
    0 ≤ modelVolumeEntropy F ε := by
  unfold modelVolumeEntropy
  apply neg_nonneg.mpr
  exact Finset.sum_nonpos (fun m hm =>
    mul_nonpos_of_nonneg_of_nonpos (modelVolume_pos F ε m).le
      (Real.log_nonpos (modelVolume_pos F ε m).le
        (modelVolume_le_one F ε m)))

theorem effectiveModelVolume_pos
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) :
    0 < effectiveModelVolume F ε := by
  unfold effectiveModelVolume
  exact Real.exp_pos _

end InfoGeometry.Inference.FiniteGibbs
