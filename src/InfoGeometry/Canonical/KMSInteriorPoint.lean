/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# KMS Interior Point — Conditional Remainder Interfaces

This file records conditional bounds for a supplied operator exponential on
the real continuous-linear endomorphisms of `H`. It does not construct an
operator exponential, a self-concordant barrier, or a Dikin-feasibility result.
Those remain separate proof obligations.

#### BUCKET 1: CLOSED FINITE THEOREMS
None in this file.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
* `bregman_remainder_bounded_of_quadratic_bound`
* `flow_uniformly_continuous_of_lipschitz_step`

#### BUCKET 3: OPEN CLOSURE DEBT
* Construct the operator exponential used by the KMS phase-axis flow.
* Prove the quadratic Bregman remainder estimate for that exponential.
* Prove the local Lipschitz continuity estimate for exponential flow steps.
-/

noncomputable section KMSInteriorPoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- An explicitly supplied operator exponential for the KMS phase-axis flow. -/
abbrev ExpOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :=
  (H →L[ℝ] H) → (H →L[ℝ] H)

/--
The conditional quadratic remainder bound for a supplied operator exponential:

  ‖exp(εK) - I - εK‖ ≤ ε²·‖K‖²   for ‖εK‖ ≤ 1.

The exponential is an explicit argument; this predicate does not construct it
or assert that it is self-concordant.
-/
def HasBregmanQuadraticBound
    (expOp : ExpOp H)
    (K : H →L[ℝ] H) : Prop :=
  ∀ ε : ℝ, ‖ε • K‖ ≤ 1 →
    ‖expOp (ε • K) - (1 : H →L[ℝ] H) - (ε • K)‖ ≤ ε ^ 2 * ‖K‖ ^ 2

/--
Local Lipschitz continuity of exponential steps along a fixed operator.
-/
def HasLocalFlowLipschitz
    (expOp : ExpOp H)
    (K : H →L[ℝ] H)
    (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ δ₁ δ₂ : ℝ, |δ₁| < 1 → |δ₂| < 1 →
      ‖expOp ((ε + δ₁) • K) - expOp ((ε + δ₂) • K)‖ ≤ C * |δ₁ - δ₂|

/-- The supplied quadratic remainder bound specializes to `ε^2` for a
    unit-norm generator and a sign-symmetric step `|ε| ≤ 1`. -/
theorem bregman_remainder_bounded_of_quadratic_bound
    (expOp : ExpOp H)
    (K : H →L[ℝ] H)
    (hquad : HasBregmanQuadraticBound expOp K)
    (hK_norm : ‖K‖ = 1)
    (ε : ℝ)
    (hε : |ε| ≤ 1) :
    ‖expOp (ε • K) - (1 : H →L[ℝ] H) - (ε • K)‖ ≤ ε ^ 2 := by
  have hstep : ‖ε • K‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, hK_norm, mul_one]
    exact hε
  have h := hquad ε hstep
  rw [hK_norm] at h
  simpa [sq, mul_one] using h

/-- A common pairwise Lipschitz bound on the unit step interval implies
uniform continuity of the exponential flow on that interval. -/
theorem flow_uniformly_continuous_of_lipschitz_step
    (expOp : ExpOp H)
    (K : H →L[ℝ] H)
    (ε : ℝ)
    (hlip : HasLocalFlowLipschitz expOp K ε) :
    UniformContinuousOn (fun δ : ℝ => expOp ((ε + δ) • K))
      {δ : ℝ | |δ| < 1} := by
  rcases hlip with ⟨C, hC, hbound⟩
  rw [Metric.uniformContinuousOn_iff]
  intro η hη
  refine ⟨η / (C + 1), div_pos hη (by linarith), ?_⟩
  intro δ₁ hδ₁ δ₂ hδ₂ hdist
  have hstep : |δ₁ - δ₂| < η / (C + 1) := by
    simpa [Real.dist_eq] using hdist
  have hscaled : C * (η / (C + 1)) < η := by
    have hden : 0 < C + 1 := by linarith
    calc
      C * (η / (C + 1)) = (C * η) / (C + 1) := by ring
      _ < η := (div_lt_iff₀ hden).2 (by nlinarith)
  have hnorm := hbound δ₁ δ₂ hδ₁ hδ₂
  have hnorm' :
      ‖expOp ((ε + δ₁) • K) - expOp ((ε + δ₂) • K)‖ < η := by
    calc
      ‖expOp ((ε + δ₁) • K) - expOp ((ε + δ₂) • K)‖
          ≤ C * |δ₁ - δ₂| := hnorm
      _ ≤ C * (η / (C + 1)) :=
        mul_le_mul_of_nonneg_left hstep.le hC
      _ < η := hscaled
  simpa [dist_eq_norm] using hnorm'
