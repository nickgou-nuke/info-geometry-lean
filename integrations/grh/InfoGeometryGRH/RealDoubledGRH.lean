/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometryGRH.VerifiedGRH
import InfoGeometry.Arithmetic.RealDoubledDirichletReadout
import InfoGeometry.Arithmetic.RealDoubledCenteredXiReadout

/-!
# GRH conclusions on the native real doubled carrier

The analytic input is the pinned external theorem imported by `VerifiedGRH`.
The target is the existing real `DoubledSpace` with `clockAxis = Jε`.
Faithful readout uses both real components of the actual Mathlib L-value;
there is no supplied zero-sector predicate or zero-chart assumption.

These theorems transport the external arithmetic conclusion. They do not
construct a Hilbert–Pólya operator or identify its spectrum with zeta zeros.
-/

noncomputable section

namespace InfoGeometry.GRHIntegration

open InfoGeometry.Krein
open InfoGeometry.Arithmetic.RealDoubledDirichletReadout
open InfoGeometry.Arithmetic.RealDoubledCenteredXiReadout

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [Nontrivial E]

/-- Every vanishing actual L-value readout in the strip has `sigma = 1/2`. -/
theorem realDirichletReadout_zero_re
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (sigma height : ℝ) (h0 : 0 < sigma) (h1 : sigma < 1)
    (hz : dirichletReadout (E := E) χ sigma height = 0) :
    sigma = 1 / 2 := by
  exact dirichletL_zeros_on_line N χ ⟨sigma, height⟩ h0 h1
    ((dirichletReadout_eq_zero_iff χ sigma height).mp hz)

/-- The principal-character pole exception is stated in real coordinates. -/
theorem realDirichletReadout_ne_zero_of_half_lt
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (sigma height : ℝ) (hs : 1 / 2 < sigma)
    (hregular : χ ≠ 1 ∨ (sigma, height) ≠ (1, 0)) :
    dirichletReadout (E := E) χ sigma height ≠ 0 := by
  apply (dirichletReadout_ne_zero_iff χ sigma height).mpr
  apply dirichletRightHalfPlaneNonvanishing N χ ⟨sigma, height⟩ hs
  rcases hregular with hχ | hcoord
  · exact Or.inl hχ
  · right
    intro h
    apply hcoord
    apply Prod.ext
    · simpa using congrArg Complex.re h
    · simpa using congrArg Complex.im h

theorem realDirichletReadout_ne_zero_off_line
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (sigma height : ℝ) (h0 : 0 < sigma) (h1 : sigma < 1)
    (hoff : sigma ≠ 1 / 2) :
    dirichletReadout (E := E) χ sigma height ≠ 0 := by
  intro hz
  exact hoff (realDirichletReadout_zero_re N χ sigma height h0 h1 hz)

/-- The actual zeta readout inherits RH, with trivial zeros excluded by the strip. -/
theorem realZetaReadout_zero_re
    (sigma height : ℝ) (h0 : 0 < sigma) (h1 : sigma < 1)
    (hz : zetaReadout (E := E) sigma height = 0) :
    sigma = 1 / 2 := by
  apply riemannHypothesis (⟨sigma, height⟩ : ℂ)
    ((zetaReadout_eq_zero_iff sigma height).mp hz)
  · rintro ⟨n, hn⟩
    have hreal := congrArg Complex.re hn
    norm_num at hreal
    nlinarith [Nat.cast_nonneg (R := ℝ) n]
  · intro hs
    have hreal := congrArg Complex.re hs
    norm_num at hreal
    linarith

/-- In centered strip coordinates the actual Xi readout vanishes only at offset zero. -/
theorem realCenteredXiReadout_zero_offset
    (offset height : ℝ) (hlo : -(1 / 2 : ℝ) < offset)
    (hhi : offset < 1 / 2)
    (hz : centeredXiReadout (E := E) offset height = 0) :
    offset = 0 := by
  have h0 : 0 < (1 / 2 : ℝ) + offset := by linarith
  have h1 : (1 / 2 : ℝ) + offset < 1 := by linarith
  have hzero : zetaReadout (E := E) ((1 / 2 : ℝ) + offset) height = 0 := by
    apply (zetaReadout_eq_zero_iff_centeredXiReadout_zero
      ((1 / 2 : ℝ) + offset) height h0 h1).mpr
    simpa using hz
  have hcritical := realZetaReadout_zero_re
    ((1 / 2 : ℝ) + offset) height h0 h1 hzero
  linarith

theorem realCenteredXiReadout_ne_zero_off_axis
    (offset height : ℝ) (hlo : -(1 / 2 : ℝ) < offset)
    (hhi : offset < 1 / 2) (hoff : offset ≠ 0) :
    centeredXiReadout (E := E) offset height ≠ 0 := by
  intro hz
  exact hoff (realCenteredXiReadout_zero_offset offset height hlo hhi hz)

end InfoGeometry.GRHIntegration
