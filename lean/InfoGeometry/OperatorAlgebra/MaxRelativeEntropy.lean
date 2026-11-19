/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Extended max-relative entropy from operator domination

The positive finite domination coefficients are infimized in `ENNReal`, so
infeasible domination has value infinity. `ENNReal.log` then gives an `EReal`
divergence in nats. This is the first formula of Eq. (150), p. 32 of
Rubboli--Regula--Berta--Lami--Tomamichel, arXiv:2611.08254v1.

The order-theoretic construction is independent of a matrix presentation.
`Quantum.MaxRelativeEntropy` supplies the actual noncommutative Kraus consumer.
No support-inverse formula, tensor additivity, or general Umegaki DPI is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.MaxRelativeEntropy

open scoped NNReal ENNReal

section OrderedScalarAction

variable {A : Type*} [Preorder A] [SMul ℝ A]

/-- Infimum of strictly positive finite coefficients dominating the first argument.
The complete-lattice convention makes an empty feasible set have value `⊤`. -/
noncomputable def dominationFactor (ρ σ : A) : ℝ≥0∞ :=
  ⨅ (c : ℝ≥0) (_ : 0 < c) (_ : ρ ≤ (c : ℝ) • σ), (c : ℝ≥0∞)

/-- Max-relative entropy, with natural logarithm and extended values. -/
noncomputable def maxRelativeEntropy (ρ σ : A) : EReal :=
  ENNReal.log (dominationFactor ρ σ)

/-- Every positive finite domination certificate gives an upper bound. -/
theorem dominationFactor_le {ρ σ : A} {c : ℝ≥0}
    (hc : 0 < c) (h : ρ ≤ (c : ℝ) • σ) : dominationFactor ρ σ ≤ c :=
  iInf_le_of_le c (iInf_le_of_le hc (iInf_le_of_le h le_rfl))

/-- Infinite domination is exactly infeasibility of all positive finite factors. -/
theorem dominationFactor_eq_top_iff (ρ σ : A) :
    dominationFactor ρ σ = ⊤ ↔ ∀ c : ℝ≥0, 0 < c → ¬ρ ≤ (c : ℝ) • σ := by
  constructor
  · intro h c hc hd
    have hb := dominationFactor_le hc hd
    rw [h] at hb
    exact ENNReal.coe_ne_top (top_le_iff.mp hb)
  · intro h
    apply le_antisymm le_top
    exact le_iInf fun c => le_iInf fun hc => le_iInf fun hd => (h c hc hd).elim

/-- Finiteness is witnessed by an actual positive finite domination coefficient. -/
theorem dominationFactor_lt_top_iff (ρ σ : A) :
    dominationFactor ρ σ < ⊤ ↔ ∃ c : ℝ≥0, 0 < c ∧ ρ ≤ (c : ℝ) • σ := by
  classical
  constructor
  · intro hfinite
    by_contra hnone
    have htop : dominationFactor ρ σ = ⊤ :=
      (dominationFactor_eq_top_iff ρ σ).mpr fun c hc hd => hnone ⟨c, hc, hd⟩
    exact (ne_of_lt hfinite) htop
  · rintro ⟨c, hc, hd⟩
    exact (dominationFactor_le hc hd).trans_lt ENNReal.coe_lt_top

/-- The extended logarithm retains the infeasible-support case. -/
theorem maxRelativeEntropy_eq_top_iff (ρ σ : A) :
    maxRelativeEntropy ρ σ = ⊤ ↔ ∀ c : ℝ≥0, 0 < c → ¬ρ ≤ (c : ℝ) • σ := by
  rw [maxRelativeEntropy, ENNReal.log_eq_top_iff, dominationFactor_eq_top_iff]

/-- Exclusion of positive infinity is witnessed by finite domination. General
inputs can still have negative infinity; normalized inputs have a separate lower bound. -/
theorem maxRelativeEntropy_lt_top_iff (ρ σ : A) :
    maxRelativeEntropy ρ σ < ⊤ ↔ ∃ c : ℝ≥0, 0 < c ∧ ρ ≤ (c : ℝ) • σ := by
  rw [maxRelativeEntropy, ENNReal.log_lt_top_iff, dominationFactor_lt_top_iff]

/-- Increasing the first operator can only increase its domination factor. -/
theorem dominationFactor_mono_left {ρ₁ ρ₂ σ : A} (h : ρ₁ ≤ ρ₂) :
    dominationFactor ρ₁ σ ≤ dominationFactor ρ₂ σ := by
  exact le_iInf fun c => le_iInf fun hc => le_iInf fun hd =>
    dominationFactor_le hc (h.trans hd)

/-- Monotonicity of max-relative entropy in its first argument. -/
theorem maxRelativeEntropy_mono_left {ρ₁ ρ₂ σ : A} (h : ρ₁ ≤ ρ₂) :
    maxRelativeEntropy ρ₁ σ ≤ maxRelativeEntropy ρ₂ σ :=
  ENNReal.log_monotone (dominationFactor_mono_left h)

end OrderedScalarAction

section PositiveMaps

variable {A B : Type*}
  [AddCommMonoid A] [PartialOrder A] [Module ℝ A]
  [AddCommMonoid B] [PartialOrder B] [Module ℝ B]

/-- A native positive linear map transports every feasible domination inequality,
and consequently contracts the extended infimum. -/
theorem dominationFactor_map_le (f : A →ₚ[ℝ] B) (ρ σ : A) :
    dominationFactor (f ρ) (f σ) ≤ dominationFactor ρ σ := by
  refine le_iInf fun c => le_iInf fun hc => le_iInf fun hd => ?_
  apply dominationFactor_le hc
  simpa only [map_smul] using f.monotone' hd

/-- Data processing for the actual extended divergence under a native positive
linear map. Trace preservation is not needed for this order-theoretic result. -/
theorem maxRelativeEntropy_map_le (f : A →ₚ[ℝ] B) (ρ σ : A) :
    maxRelativeEntropy (f ρ) (f σ) ≤ maxRelativeEntropy ρ σ :=
  ENNReal.log_monotone (dominationFactor_map_le f ρ σ)

/-- A normalized positive functional rules out domination factors below one. -/
theorem one_le_dominationFactor_of_normalized (τ : A →ₚ[ℝ] ℝ)
    {ρ σ : A} (hρ : τ ρ = 1) (hσ : τ σ = 1) :
    1 ≤ dominationFactor ρ σ := by
  refine le_iInf fun c => le_iInf fun _ => le_iInf fun hd => ?_
  have hc : (1 : ℝ) ≤ c := by
    simpa only [map_smul, hρ, hσ, smul_eq_mul, mul_one] using τ.monotone' hd
  exact_mod_cast hc

/-- Nonnegativity on pairs normalized by the same positive functional. -/
theorem maxRelativeEntropy_nonneg_of_normalized (τ : A →ₚ[ℝ] ℝ)
    {ρ σ : A} (hρ : τ ρ = 1) (hσ : τ σ = 1) :
    0 ≤ maxRelativeEntropy ρ σ :=
  ENNReal.zero_le_log_iff.mpr (one_le_dominationFactor_of_normalized τ hρ hσ)

/-- The domination factor of a normalized element against itself is exactly one. -/
theorem dominationFactor_self_of_normalized (τ : A →ₚ[ℝ] ℝ)
    {ρ : A} (hρ : τ ρ = 1) : dominationFactor ρ ρ = 1 := by
  apply le_antisymm
  · simpa only [ENNReal.coe_one] using
      (dominationFactor_le (ρ := ρ) (σ := ρ) (c := 1) zero_lt_one (by simp))
  · exact one_le_dominationFactor_of_normalized τ hρ hρ

/-- Reflexivity of the normalized divergence. -/
theorem maxRelativeEntropy_self_of_normalized (τ : A →ₚ[ℝ] ℝ)
    {ρ : A} (hρ : τ ρ = 1) : maxRelativeEntropy ρ ρ = 0 := by
  rw [maxRelativeEntropy, dominationFactor_self_of_normalized τ hρ, ENNReal.log_one]

end PositiveMaps

section Antitonicity

variable {A : Type*} [AddCommMonoid A] [PartialOrder A] [Module ℝ A]
  [PosSMulMono ℝ A]

/-- Increasing the reference operator weakens domination requirements. -/
theorem dominationFactor_antitone_right {ρ σ₁ σ₂ : A} (h : σ₁ ≤ σ₂) :
    dominationFactor ρ σ₂ ≤ dominationFactor ρ σ₁ := by
  exact le_iInf fun c => le_iInf fun hc => le_iInf fun hd =>
    dominationFactor_le hc (hd.trans (smul_le_smul_of_nonneg_left h c.property))

/-- Antitonicity of max-relative entropy in its reference argument. -/
theorem maxRelativeEntropy_antitone_right {ρ σ₁ σ₂ : A} (h : σ₁ ≤ σ₂) :
    maxRelativeEntropy ρ σ₂ ≤ maxRelativeEntropy ρ σ₁ :=
  ENNReal.log_monotone (dominationFactor_antitone_right h)

end Antitonicity

end InfoGeometry.OperatorAlgebra.MaxRelativeEntropy
