/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumGeometry.Projective.QGT
import InfoGeometry.QuantumGeometry.TensorBridge
import InfoGeometry.Canonical.OnsagerReciprocity
import InfoGeometry.Canonical.BKMCommutatorDikin

/-!
# Operator Cramér–Rao Uncertainty Principle with Commutator, Onsager Theory

This module restates the Robertson–Schrödinger / QGT commutator uncertainty bound
in Onsager metriplectic language, using only real-valued quantities:

- the **symmetric dissipative sector** (Onsager reciprocity) is the Cramér–Rao /
  Fisher variance `g(X,X) = fubiniStudyMetric ψ X X`,
- the **skew reversible sector** is the commutator / Berry curvature bracket
  `Ω(X,Y) = berryCurvature ψ X Y : ℝ`,
- the **genuine** QGT Cauchy–Schwarz inequality
  `|QGT(X,Y)|² ≤ g(X,X)·g(Y,Y)` (proved natively from `norm_inner_le_norm` on
  horizontal projections, not assumed) together with the QGT Pythagorean split
  `|QGT|² = g² + Ω²/4` yields
    `g(X,X)·g(Y,Y) ≥ (1/4)·Ω(X,Y)²`.

This is the operator Cramér–Rao uncertainty principle with the commutator as the
reversible (Onsager antisymmetric) contribution. No scalar/diagonal/commutative
toys, no `Complex.I` / bivactor rotor: all statements are real-valued and uniform
over arbitrary operators on a complex Hilbert space, on a **normalized** state.

-/

noncomputable section

namespace InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty

open InfoGeometry.QuantumGeometry.Projective
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H

/-- Onsager dissipative (symmetric) metric: the Cramér–Rao / Fisher variance
sector. By Onsager reciprocity this is symmetric in its two arguments. -/
def onsagerDissipativeMetric (ψ : NormalizedState H) (X Y : EndH) : ℝ := fubiniStudyMetric ψ X Y

/-- Onsager reversible (skew) bracket: the commutator / Berry curvature sector. -/
def onsagerReversibleBracket (ψ : NormalizedState H) (X Y : EndH) : ℝ := berryCurvature ψ X Y

/-- The Cramér–Rao inequality (genuine QGT Cauchy–Schwarz).
The product of dissipative variances bounds the squared QGT magnitude:
`g(X,X)·g(Y,Y) ≥ |QGT(X,Y)|²`.
This is derived natively from Mathlib's `norm_inner_le_norm` on horizontal
projections (`Projective.QGT.QGT_cauchy_schwarz`), not assumed. -/
theorem cramerRao_QGT_bound (ψ : NormalizedState H) (X Y : EndH) :
    fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y ≥ Complex.normSq (QGT ψ X Y) := by
  have h : Complex.normSq (QGT ψ X Y) ≤ fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y :=
    InfoGeometry.QuantumGeometry.Projective.QGT_cauchy_schwarz ψ X Y
  linarith

/-- Operator Cramér–Rao commutator uncertainty principle (Onsager form).
The product of the Onsager dissipative variances is bounded below by one
quarter of the squared reversible commutator bracket:
    g(X,X)·g(Y,Y) ≥ (1/4)·Ω(X,Y)².

Derived genuinely:
  g(X,X)·g(Y,Y) ≥ |QGT(X,Y)|²                      (QGT Cauchy–Schwarz)
  |QGT(X,Y)|² = g(X,Y)² + (1/4)·Ω(X,Y)²            (QGT Pythagorean split)
  hence g(X,X)·g(Y,Y) ≥ (1/4)·Ω(X,Y)²              (drop g(X,Y)² ≥ 0).
-/
theorem cramerRao_commutator_uncertainty_bound (ψ : NormalizedState H) (X Y : EndH) :
    fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y ≥
      (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X Y) ^ 2 := by
  have h_cs : Complex.normSq (QGT ψ X Y) ≤ fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y :=
    InfoGeometry.QuantumGeometry.Projective.QGT_cauchy_schwarz ψ X Y
  have h_split : Complex.normSq (QGT ψ X Y) =
      (fubiniStudyMetric ψ X Y) ^ 2 + (1 / 4 : ℝ) * (berryCurvature ψ X Y) ^ 2 := by
    rw [InfoGeometry.QuantumGeometry.Projective.QGT_normSq_decomposition]
  -- Chain: g(X,X)·g(Y,Y) ≥ |QGT|² ≥ Ω²/4.
  have h₁ : (1 / 4 : ℝ) * (berryCurvature ψ X Y) ^ 2 ≤
      fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y := by
    linarith [sq_nonneg (fubiniStudyMetric ψ X Y)]
  simpa [onsagerReversibleBracket] using h₁

/-- Onsager split of the QGT modulus: `|QGT(X,Y)|² = g(X,Y)² + (1/4)·Ω(X,Y)²`.
The dissipative (Cramér–Rao) sector and the reversible (commutator) sector are
orthogonal, so the reversible bracket contributes a definite nonnegative term. -/
theorem onsager_QGT_split (ψ : NormalizedState H) (X Y : EndH) :
    Complex.normSq (QGT ψ X Y) =
      (fubiniStudyMetric ψ X Y) ^ 2 + (1 / 4 : ℝ) *
        (onsagerReversibleBracket ψ X Y) ^ 2 := by
  have h : Complex.normSq (QGT ψ X Y) =
      (fubiniStudyMetric ψ X Y) ^ 2 + (1 / 4 : ℝ) * (berryCurvature ψ X Y) ^ 2 := by
    rw [InfoGeometry.QuantumGeometry.Projective.QGT_normSq_decomposition]
  simpa [onsagerReversibleBracket] using h

/-- Full Metriplectic Operator Cramér–Rao / Robertson–Schrödinger Bound:
`g(X,X)·g(Y,Y) ≥ g(X,Y)² + (1/4)·Ω(X,Y)²`.
Combines the dissipative Fisher covariance leg `g(X,Y)²` and the reversible Berry
commutator leg `(1/4)·Ω(X,Y)²` into a single Pythagorean lower bound. -/
theorem cramerRao_metriplectic_full_bound (ψ : NormalizedState H) (X Y : EndH) :
    onsagerDissipativeMetric ψ X X * onsagerDissipativeMetric ψ Y Y ≥
      (onsagerDissipativeMetric ψ X Y) ^ 2 +
        (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X Y) ^ 2 := by
  have h_cs : Complex.normSq (QGT ψ X Y) ≤ fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y :=
    InfoGeometry.QuantumGeometry.Projective.QGT_cauchy_schwarz ψ X Y
  have h_split : Complex.normSq (QGT ψ X Y) =
      (fubiniStudyMetric ψ X Y) ^ 2 + (1 / 4 : ℝ) * (berryCurvature ψ X Y) ^ 2 := by
    rw [InfoGeometry.QuantumGeometry.Projective.QGT_normSq_decomposition]
  have h₁ : (fubiniStudyMetric ψ X Y) ^ 2 + (1 / 4 : ℝ) * (berryCurvature ψ X Y) ^ 2 ≤
      fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y := by
    linarith
  simpa [onsagerDissipativeMetric, onsagerReversibleBracket] using h₁

/-- Classical Cramér–Rao Projection of the Metriplectic Bound:
Discarding the nonnegative reversible Berry commutator term `(1/4)·Ω(X,Y)² ≥ 0`
yields the classical statistical covariance inequality `g(X,X)·g(Y,Y) ≥ g(X,Y)²`. -/
theorem cramerRao_classical_covariance_bound (ψ : NormalizedState H) (X Y : EndH) :
    onsagerDissipativeMetric ψ X X * onsagerDissipativeMetric ψ Y Y ≥
      (onsagerDissipativeMetric ψ X Y) ^ 2 := by
  have h_full := cramerRao_metriplectic_full_bound ψ X Y
  have h_nonneg : 0 ≤ (1 / 4 : ℝ) * (onsagerReversibleBracket ψ X Y) ^ 2 := by
    positivity
  linarith

/-- For skew-adjoint generators, the reversible bracket is exactly the
commutator expectation, giving the Robertson–Schrödinger form:
    g(X,X)·g(Y,Y) ≥ (1/4)·|⟪ψ,[X,Y]ψ⟫|².
-/
theorem cramerRao_robertson_schrodinger_bound (ψ : NormalizedState H) {X Y : EndH}
    (hX : ContinuousLinearMap.adjoint X = -X)
    (hY : ContinuousLinearMap.adjoint Y = -Y) :
    fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y ≥
      (1 / 4 : ℝ) * Complex.normSq (⟪ψ.vec, (opCommutator X Y ψ.vec)⟫_ℂ) := by
  have h : fubiniStudyMetric ψ X X * fubiniStudyMetric ψ Y Y ≥
      (1 / 4 : ℝ) * Complex.normSq (⟪ψ.vec, (opCommutator X Y ψ.vec)⟫_ℂ) := by
    have h₁ := InfoGeometry.QuantumGeometry.TensorBridge.robertson_schrodinger_full_uncertainty ψ X Y hX hY
    exact h₁.2
  exact h

end InfoGeometry.Canonical.CramerRaoOnsagerCommutatorUncertainty

end
