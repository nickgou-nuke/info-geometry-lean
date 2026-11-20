/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Inference.FiniteGibbsThermodynamicIdentity
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fin.VecNotation

/-!
# Entropy loss in an imperfect classical reset

The two outcomes have probabilities `p` and `1-p`. Entropy is in natural-log
units and uses Mathlib's `Real.binEntropy`. The energy-valued threshold is the
entropy loss from an initially uniform bit, multiplied by `kB * T`.

The heat theorem states its bath/total-entropy assumption explicitly. No
microscopic dynamics, empirical measurement, or stored rest mass is inferred.
See `docs/LANDAUER_EXPERIMENTAL_CONTRACT.md` for source and scope.
-/

noncomputable section

namespace InfoGeometry.Physics.InformationEnergy.BinaryErasure

open scoped BigOperators
open InfoGeometry.Inference InfoGeometry.Inference.FiniteGibbs

/-- Energy-valued entropy deficit relative to a uniform classical bit. -/
def erasureCost (kB T p : ℝ) : ℝ :=
  kB * T * (Real.log 2 - Real.binEntropy p)

/-- The existing finite Shannon functional agrees with native binary entropy. -/
theorem entropyOf_binary (p : ℝ) :
    entropyOf (![p, 1 - p] : Fin 2 → ℝ) = Real.binEntropy p := by
  simp [entropyOf, Fin.sum_univ_two, Real.binEntropy, Real.log_inv]
  ring

/-- The threshold is exactly temperature times relative entropy to the uniform bit. -/
theorem erasureCost_eq_relativeEntropy (kB T p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    erasureCost kB T p = kB * T *
      finiteRelativeEntropy (![p, 1 - p] : Fin 2 → ℝ) (fun _ => (1 / 2 : ℝ)) := by
  have hpos : ∀ i : Fin 2, 0 < (![p, 1 - p] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i
    · simpa using hp
    · simpa using sub_pos.mpr hp1
  have hsum : ∑ i : Fin 2, (![p, 1 - p] : Fin 2 → ℝ) i = 1 := by
    simp [Fin.sum_univ_two]
  have hkl := finiteRelativeEntropy_to_uniform_eq_log_card_sub_entropyOf
    (![p, 1 - p] : Fin 2 → ℝ) hpos hsum
  simpa [erasureCost, entropyOf_binary] using congrArg (fun x : ℝ => kB * T * x) hkl.symm

/-- The entropy balance gives a lower bound on heat delivered to the bath. -/
theorem entropy_balance_iff_heat_bound (kB T p Q : ℝ) (hT : 0 < T) :
    0 ≤ kB * (Real.binEntropy p - Real.log 2) + Q / T ↔
      erasureCost kB T p ≤ Q := by
  have hcancel : (Q / T) * T = Q := div_mul_cancel₀ Q hT.ne'
  constructor
  · intro h
    have hscaled := mul_nonneg h hT.le
    dsimp [erasureCost]
    nlinarith only [hscaled, hcancel]
  · intro h
    apply (mul_nonneg_iff_of_pos_right hT).mp
    dsimp [erasureCost] at h
    nlinarith only [h, hcancel]

/-- Imperfect erasure interpolates between zero and the complete-reset threshold. -/
theorem erasureCost_bounds (kB T p : ℝ) (hkB : 0 ≤ kB) (hT : 0 ≤ T)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ erasureCost kB T p ∧ erasureCost kB T p ≤ kB * T * Real.log 2 := by
  have hscale : 0 ≤ kB * T := mul_nonneg hkB hT
  have hentropy := Real.binEntropy_nonneg hp hp1
  have hmax := Real.binEntropy_le_log_two (p := p)
  constructor
  · exact mul_nonneg hscale (sub_nonneg.mpr hmax)
  · exact mul_le_mul_of_nonneg_left (sub_le_self _ hentropy) hscale

/-- With positive thermal scale, zero threshold means a still-uniform memory. -/
theorem erasureCost_eq_zero_iff (kB T p : ℝ) (hkB : 0 < kB) (hT : 0 < T) :
    erasureCost kB T p = 0 ↔ p = 2⁻¹ := by
  have hscale : kB * T ≠ 0 := (mul_pos hkB hT).ne'
  constructor
  · intro h
    have hgap : Real.log 2 - Real.binEntropy p = 0 :=
      (mul_eq_zero.mp h).resolve_left hscale
    apply Real.binEntropy_eq_log_two.mp
    linarith only [hgap]
  · intro hp
    simp [erasureCost, hp]

/-- The full threshold is reached exactly at deterministic binary endpoints. -/
theorem erasureCost_eq_full_iff (kB T p : ℝ) (hkB : 0 < kB) (hT : 0 < T) :
    erasureCost kB T p = kB * T * Real.log 2 ↔ p = 0 ∨ p = 1 := by
  have hscale : kB * T ≠ 0 := (mul_pos hkB hT).ne'
  constructor
  · intro h
    have hgap := mul_left_cancel₀ hscale h
    apply Real.binEntropy_eq_zero.mp
    change Real.log 2 - Real.binEntropy p = Real.log 2 at hgap
    linarith only [hgap]
  · rintro (rfl | rfl) <;> simp [erasureCost]

/-- Better reset reliability strictly increases the entropy-loss threshold. -/
theorem erasureCost_strictMonoOn (kB T : ℝ) (hkB : 0 < kB) (hT : 0 < T) :
    StrictMonoOn (erasureCost kB T) (Set.Icc (2⁻¹ : ℝ) 1) := by
  intro p hp q hq hpq
  have hentropy := Real.binEntropy_strictAntiOn hp hq hpq
  exact mul_lt_mul_of_pos_left (sub_lt_sub_left hentropy _) (mul_pos hkB hT)

/-- Resetting to the opposite designated bit has the same entropy loss. -/
theorem erasureCost_complement (kB T p : ℝ) :
    erasureCost kB T (1 - p) = erasureCost kB T p := by
  simp only [erasureCost, Real.binEntropy_one_sub]

end InfoGeometry.Physics.InformationEnergy.BinaryErasure
