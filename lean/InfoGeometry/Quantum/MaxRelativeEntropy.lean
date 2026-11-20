/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.MaxRelativeEntropy
import InfoGeometry.Quantum.PositiveEffectOrder

/-!
# Max-relative entropy for full complex matrices

This owner specializes the extended operator-domination divergence to the
existing Kraus maps and native Loewner order. It also proves the measurement
form of its feasible-factor infimum and explicit sufficient conditions for
infinite divergence. The latter are support obstructions, not a converse
finite-dimensional support theorem.

Source: arXiv:2611.08254v1, Eq. (150), printed page 32. Values are in nats.
-/

noncomputable section
namespace InfoGeometry.Quantum.MaxRelativeEntropy

open Matrix
open InfoGeometry.OperatorAlgebra.MaxRelativeEntropy
open scoped ComplexOrder MatrixOrder NNReal ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n]

private def realTracePositiveMap : Matrix n n ℂ →ₚ[ℝ] ℝ where
  toLinearMap := Complex.reCLM.toLinearMap.comp (Matrix.traceLinearMap n ℝ ℂ)
  monotone' := fun _ _ h =>
    Complex.re_le_re ((Matrix.tracePositiveLinearMap n ℝ ℂ).monotone' h)

/-- Trace-one matrices have domination factor at least one. In particular,
normalized positive states cannot acquire a spurious negative divergence. -/
theorem one_le_dominationFactor {ρ σ : Matrix n n ℂ}
    (hρ : trace ρ = 1) (hσ : trace σ = 1) :
    1 ≤ dominationFactor ρ σ := by
  apply one_le_dominationFactor_of_normalized realTracePositiveMap
  · change (trace ρ).re = 1
    simp [hρ]
  · change (trace σ).re = 1
    simp [hσ]

/-- Nonnegativity of the extended divergence on trace-one matrices. -/
theorem maxRelativeEntropy_nonneg {ρ σ : Matrix n n ℂ}
    (hρ : trace ρ = 1) (hσ : trace σ = 1) :
    0 ≤ maxRelativeEntropy ρ σ :=
  ENNReal.zero_le_log_iff.mpr (one_le_dominationFactor hρ hσ)

/-- Self-divergence vanishes for a normalized matrix. -/
theorem maxRelativeEntropy_self {ρ : Matrix n n ℂ} (hρ : trace ρ = 1) :
    maxRelativeEntropy ρ ρ = 0 := by
  apply maxRelativeEntropy_self_of_normalized realTracePositiveMap
  change (trace ρ).re = 1
  simp [hρ]

private def krausPositiveMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) : Matrix n n ℂ →ₚ[ℝ] Matrix n n ℂ where
  toLinearMap := (Choi.krausMap V).restrictScalars ℝ
  monotone' := BoundaryConditioning.krausMap_monotone V

/-- The existing Kraus map contracts the actual extended domination factor.
The order of `V i * ρ * star (V i)` is retained by its native owner. -/
theorem dominationFactor_kraus_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) (ρ σ : Matrix n n ℂ) :
    dominationFactor (Choi.krausMap V ρ) (Choi.krausMap V σ) ≤
      dominationFactor ρ σ :=
  dominationFactor_map_le (krausPositiveMap V) ρ σ

/-- Data processing for max-relative entropy under actual finite Kraus maps.
No trace-preservation assumption is needed for domination transport. -/
theorem maxRelativeEntropy_kraus_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) (ρ σ : Matrix n n ℂ) :
    maxRelativeEntropy (Choi.krausMap V ρ) (Choi.krausMap V σ) ≤
      maxRelativeEntropy ρ σ :=
  maxRelativeEntropy_map_le (krausPositiveMap V) ρ σ

/-- Kraus completeness supplies the normalized-state domain of channel DPI. -/
theorem kraus_preserves_state {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) (hV : (∑ i, star (V i) * V i) = 1)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    (Choi.krausMap V ρ).PosSemidef ∧ trace (Choi.krausMap V ρ) = 1 :=
  ⟨Choi.krausMap_posSemidef V hρ,
    (Choi.trace_krausMap_of_completeness V hV ρ).trans htr⟩

/-- On trace-one inputs a trace-preserving Kraus map gives a nonnegative
output divergence bounded by the input divergence. -/
theorem maxRelativeEntropy_kraus_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) (hV : (∑ i, star (V i) * V i) = 1)
    {ρ σ : Matrix n n ℂ} (hρ : trace ρ = 1) (hσ : trace σ = 1) :
    0 ≤ maxRelativeEntropy (Choi.krausMap V ρ) (Choi.krausMap V σ) ∧
      maxRelativeEntropy (Choi.krausMap V ρ) (Choi.krausMap V σ) ≤
        maxRelativeEntropy ρ σ :=
  ⟨maxRelativeEntropy_nonneg
      ((Choi.trace_krausMap_of_completeness V hV ρ).trans hρ)
      ((Choi.trace_krausMap_of_completeness V hV σ).trans hσ),
    maxRelativeEntropy_kraus_le V ρ σ⟩

/-- The domination factor is the infimum of positive factors bounding every
measurement-effect likelihood. No division by a possibly zero Born weight is used. -/
theorem dominationFactor_eq_iInf_born_bounds {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    dominationFactor ρ σ =
      ⨅ (c : ℝ≥0) (_ : 0 < c)
        (_ : ∀ E : Matrix n n ℂ, 0 ≤ E ∧ E ≤ 1 →
          trace (E * ρ) ≤ (c : ℂ) * trace (E * σ)), (c : ℝ≥0∞) := by
  unfold dominationFactor
  refine iInf_congr fun c => iInf_congr fun _ => ?_
  rw [PositiveEffectOrder.le_smul_iff_born_le_effects hρ hσ (c : ℝ) c.property]

/-- A positive test with zero reference weight and strictly positive input
weight rules out every finite domination factor. -/
theorem maxRelativeEntropy_eq_top_of_trace_witness {ρ σ E : Matrix n n ℂ}
    (hE : E.PosSemidef) (hσ : trace (σ * E) = 0)
    (hρ : 0 < trace (ρ * E)) : maxRelativeEntropy ρ σ = ⊤ := by
  apply (maxRelativeEntropy_eq_top_iff ρ σ).mpr
  intro c _ hd
  have ht := PositiveEffectOrder.trace_mul_le_of_le hd hE
  rw [Matrix.smul_mul, trace_smul, hσ, smul_zero] at ht
  exact (not_le_of_gt hρ) ht

/-- A kernel vector of the reference that is not a kernel vector of the
positive input is a concrete support obstruction to finite max-relative entropy. -/
theorem maxRelativeEntropy_eq_top_of_kernel_witness {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (x : n → ℂ) (hσx : σ *ᵥ x = 0)
    (hρx : ρ *ᵥ x ≠ 0) : maxRelativeEntropy ρ σ = ⊤ := by
  apply maxRelativeEntropy_eq_top_of_trace_witness
    (E := vecMulVec x (star x)) (posSemidef_vecMulVec_self_star x)
  · rw [PositiveEffectOrder.trace_mul_vecMulVec_self_star, hσx, dotProduct_zero]
  · rw [PositiveEffectOrder.trace_mul_vecMulVec_self_star]
    exact lt_of_le_of_ne (hρ.dotProduct_mulVec_nonneg x)
      (Ne.symm (hρx ∘ hρ.dotProduct_mulVec_zero_iff.mp))

end InfoGeometry.Quantum.MaxRelativeEntropy
