/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SubgroupCompressionVariance
import InfoGeometry.LLM.WalshCharacterGeometry
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Pointwise binary logarithms under finite subgroup compression

The logarithmic operator is multiplication by the actual function
`x ↦ log (1 + s * χ x)` on `G → ℝ`. For an order-two real character and
`|s| < 1`, the existing scalar logarithm theorem supplies its exact operator
normal form with coefficient `Real.artanh s`. The finite subgroup average
then removes its nontrivial first character moment while retaining the
squared coefficient in the second compression defect.

This is a logarithm multiplication operator in the full endomorphism algebra.
It does not identify that defect with a BKM metric or invoke a matrix-log
functional calculus. The nonzero conclusion has the exact condition `s ≠ 0`.
-/

noncomputable section

namespace InfoGeometry.LLM.SubgroupLogCompression

open TannakaDuality.FiniteGroup
open InfoGeometry.Algebra.SubgroupCompressionVariance
open InfoGeometry.LLM.WalshCharacterGeometry

variable {G : Type} [Group G]

/-- The actual pointwise logarithm multiplication operator. -/
def logCharacterMultiplier (χ : G →* ℝ) (s : ℝ) : Module.End ℝ (G → ℝ) :=
  LinearMap.mulLeft ℝ (fun x => Real.log (1 + s * χ x))

/-- Two-point logarithm interpolation gives an equality of actual operators. -/
theorem logCharacterMultiplier_normal_form (χ : G →* ℝ) (s : ℝ)
    (hs : |s| < 1) (hχ : ∀ x : G, χ x ^ 2 = 1) :
    logCharacterMultiplier χ s =
      (Real.log (1 - s ^ 2) / 2) • (1 : Module.End ℝ (G → ℝ)) +
        Real.artanh s • LinearMap.mulLeft ℝ (χ : G → ℝ) := by
  ext f x
  change Real.log (1 + s * χ x) * f x =
    (Real.log (1 - s ^ 2) / 2) * f x + Real.artanh s * (χ x * f x)
  rw [log_one_add_mul_of_sq_eq_one hs (hχ x),
    Real.artanh_eq_half_log ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩]
  ring

variable (H : Subgroup G) [Fintype H] [Invertible (Fintype.card H : ℝ)]

local notation "ρH" => MonoidHom.comp (rightRegular (k := ℝ) (G := G)) (Subgroup.subtype H)
local notation "P" => Representation.averageMap ρH

/-- A character nontrivial on `H` leaves only the mean logarithm after compression. -/
theorem subgroup_log_compression (χ : G →* ℝ) (s : ℝ)
    (hs : |s| < 1) (hχ : ∀ x : G, χ x ^ 2 = 1)
    (hmicro : ∃ h : H, χ (h : G) ≠ 1) :
    P * logCharacterMultiplier χ s * P = (Real.log (1 - s ^ 2) / 2) • P := by
  rw [logCharacterMultiplier_normal_form χ s hs hχ]
  exact subgroup_binary_compression H χ (Real.log (1 - s ^ 2) / 2)
    (Real.artanh s) hmicro

/-- The exact second compression defect of the actual logarithmic operator. -/
theorem subgroup_log_compression_variance (χ : G →* ℝ) (s : ℝ)
    (hs : |s| < 1) (hχ : ∀ x : G, χ x ^ 2 = 1)
    (hmicro : ∃ h : H, χ (h : G) ≠ 1) :
    let L := logCharacterMultiplier χ s
    P * (L * L) * P - (P * L * P) * (P * L * P) = (Real.artanh s) ^ 2 • P := by
  dsimp only
  rw [logCharacterMultiplier_normal_form χ s hs hχ, pow_two (Real.artanh s)]
  exact subgroup_binary_compression_variance H χ (Real.log (1 - s ^ 2) / 2)
    (Real.artanh s) (fun x => by simpa only [pow_two] using hχ x) hmicro

/-- Strict survival occurs precisely for a nonzero parameter within `(-1,1)`. -/
theorem subgroup_log_variance_ne_zero_iff (χ : G →* ℝ) (s : ℝ)
    (hs : |s| < 1) (hχ : ∀ x : G, χ x ^ 2 = 1)
    (hmicro : ∃ h : H, χ (h : G) ≠ 1) :
    let L := logCharacterMultiplier χ s
    P * (L * L) * P - (P * L * P) * (P * L * P) ≠ 0 ↔ s ≠ 0 := by
  dsimp only
  rw [logCharacterMultiplier_normal_form χ s hs hχ]
  refine (subgroup_binary_variance_ne_zero_iff H χ (Real.log (1 - s ^ 2) / 2)
    (Real.artanh s) (fun x => by simpa only [pow_two] using hχ x) hmicro).trans ?_
  constructor
  · intro ha hs0
    apply ha
    rw [hs0, Real.artanh_zero]
  · intro hs0 ha
    apply hs0
    have ht := Real.tanh_artanh (abs_lt.mp hs)
    simpa only [ha, Real.tanh_zero] using ht.symm

end InfoGeometry.LLM.SubgroupLogCompression
