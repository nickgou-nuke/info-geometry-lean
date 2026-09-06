/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.
-/

import InfoGeometry.Inference.FiniteGibbsSimplexVolume
import InfoGeometry.Inference.FiniteGibbsThermodynamicIdentity

/-!
# Model-volume entropy bridge

The normalized model-volume distribution is an ordinary finite probability
vector.  This module transfers the generic entropy-volume bounds to the
model-family decomposition layer.
-/

namespace InfoGeometry.Inference.FiniteGibbs

open scoped BigOperators

variable {ModelId Data : Type*} [Fintype ModelId] [Nonempty ModelId]
  [Fintype Data] [Nonempty Data]

/-- The model-volume entropy is the generic entropy of its volume vector. -/
theorem modelVolumeEntropy_eq_entropyOf
    (F : ModelFamily (ModelId := ModelId) (Data := Data)) (ε : ℝ) :
    modelVolumeEntropy F ε = entropyOf (modelVolume F ε) := by
  rfl

/-- Model-volume entropy is bounded by the logarithm of the model count. -/
theorem modelVolumeEntropy_le_log_card
    (F : ModelFamily (ModelId := ModelId) (Data := Data)) (ε : ℝ) :
    modelVolumeEntropy F ε ≤ Real.log (Fintype.card ModelId) := by
  rw [modelVolumeEntropy_eq_entropyOf]
  exact entropyOf_le_log_card (modelVolume F ε)
    (fun m => modelVolume_pos F ε m)
    (modelVolumes_sum_one F ε)

/-- Maximum model-volume entropy occurs exactly at uniform model volume. -/
theorem modelVolumeEntropy_eq_log_card_iff_uniform
    (F : ModelFamily (ModelId := ModelId) (Data := Data)) (ε : ℝ) :
    modelVolumeEntropy F ε = Real.log (Fintype.card ModelId) ↔
      ∀ m : ModelId, modelVolume F ε m = 1 / (Fintype.card ModelId : ℝ) := by
  rw [modelVolumeEntropy_eq_entropyOf]
  exact entropyOf_eq_log_card_iff_uniform (modelVolume F ε)
    (fun m => modelVolume_pos F ε m)
    (modelVolumes_sum_one F ε)

/-- Effective model volume is bounded by the number of available models. -/
theorem effectiveModelVolume_le_card
    (F : ModelFamily (ModelId := ModelId) (Data := Data)) (ε : ℝ) :
    effectiveModelVolume F ε ≤ Fintype.card ModelId := by
  have hcard : 0 < (Fintype.card ModelId : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [effectiveModelVolume, ← Real.exp_log hcard]
  exact Real.exp_le_exp.mpr (modelVolumeEntropy_le_log_card F ε)

/-- Effective model volume reaches the model count exactly at uniform volume. -/
theorem effectiveModelVolume_eq_card_iff_uniform
    (F : ModelFamily (ModelId := ModelId) (Data := Data)) (ε : ℝ) :
    effectiveModelVolume F ε = Fintype.card ModelId ↔
      ∀ m : ModelId, modelVolume F ε m = 1 / (Fintype.card ModelId : ℝ) := by
  have hcard : 0 < (Fintype.card ModelId : ℝ) := by
    exact_mod_cast Fintype.card_pos
  constructor
  · intro h
    apply (modelVolumeEntropy_eq_log_card_iff_uniform F ε).mp
    have hexp : Real.exp (modelVolumeEntropy F ε) =
        Real.exp (Real.log (Fintype.card ModelId)) := by
      rw [Real.exp_log hcard]
      exact h
    exact Real.exp_injective hexp
  · intro huniform
    rw [effectiveModelVolume]
    rw [(modelVolumeEntropy_eq_log_card_iff_uniform F ε).mpr huniform]
    exact Real.exp_log hcard

end InfoGeometry.Inference.FiniteGibbs
