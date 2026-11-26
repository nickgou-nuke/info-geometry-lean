/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Real Schwartz position/derivative uncertainty

The coefficient space is a positive real inner-product space. Position
multiplication and differentiation act on Schwartz space, an explicit common
invariant domain for the unbounded operators on `L2`.

The integration-by-parts identity is proved from Mathlib's Schwartz API;
no uncertainty inequality or commutator expectation is assumed. The position
center is arbitrary and the signal need not be normalized.

The real analytic core is recovered from the real section of the earlier
`SchwartzUncertainty.lean` development (PR #376), with independent Mathlib
imports and no complex scalar declarations.
-/

noncomputable section

namespace InfoGeometry.Analysis.RealSchwartzUncertainty

open MeasureTheory

section Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem real_inner_toL2 (f g : SchwartzMap ℝ H) :
    inner ℝ (f.toLp 2 volume) (g.toLp 2 volume) =
      ∫ x : ℝ, inner ℝ (f x) (g x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hf hg
  rw [hf, hg]

private theorem toL2_add (f g : SchwartzMap ℝ H) :
    (f + g).toLp 2 volume = f.toLp 2 volume + g.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℝ H 2 volume).map_add f g

private theorem toL2_sub (f g : SchwartzMap ℝ H) :
    (f - g).toLp 2 volume = f.toLp 2 volume - g.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℝ H 2 volume).map_sub f g

private theorem toL2_smul (b : ℝ) (f : SchwartzMap ℝ H) :
    (b • f).toLp 2 volume = b • f.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℝ H 2 volume).map_smul b f

/-- The product rule on Schwartz space: differentiating `(x - a) • f x`
adds one copy of `f` to position multiplication of its derivative. -/
theorem deriv_position (f : SchwartzMap ℝ H) (a : ℝ) :
    SchwartzMap.derivCLM ℝ H
        (SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f) =
      f + SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a)
        (SchwartzMap.derivCLM ℝ H f) := by
  have hg : (fun x : ℝ => x - a).HasTemperateGrowth := by fun_prop
  ext x
  simp only [SchwartzMap.derivCLM_apply, add_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg]
  rw [SchwartzMap.smulLeftCLM_apply hg]
  simpa only [id_eq, Pi.smul_def', one_smul, add_comm] using
    (((hasDerivAt_id x).sub_const a).smul (f.hasDerivAt x)).deriv

/-- Integration by parts identifies the position/derivative pairing exactly.
All boundary and integrability conditions follow from Schwartz regularity. -/
theorem real_inner_position_deriv (f : SchwartzMap ℝ H) (a : ℝ) :
    inner ℝ
        ((SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume)
        ((SchwartzMap.derivCLM ℝ H f).toLp 2 volume) =
      -(1 / 2 : ℝ) * ‖f.toLp 2 volume‖ ^ 2 := by
  let q := SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f
  let d := SchwartzMap.derivCLM ℝ H f
  have hg : (fun x : ℝ => x - a).HasTemperateGrowth := by fun_prop
  have hmove :
      inner ℝ (f.toLp 2 volume)
          ((SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) d).toLp 2 volume) =
        inner ℝ (q.toLp 2 volume) (d.toLp 2 volume) := by
    rw [real_inner_toL2, real_inner_toL2]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [q, SchwartzMap.smulLeftCLM_apply_apply hg,
      real_inner_smul_left, real_inner_smul_right]
  have hibp :
      inner ℝ (f.toLp 2 volume) ((SchwartzMap.derivCLM ℝ H q).toLp 2 volume) =
        -inner ℝ (d.toLp 2 volume) (q.toLp 2 volume) := by
    rw [real_inner_toL2, real_inner_toL2]
    exact SchwartzMap.integral_bilinear_deriv_right_eq_neg_left f q (innerSL ℝ)
  have hderiv : SchwartzMap.derivCLM ℝ H q =
      f + SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) d :=
    deriv_position f a
  rw [hderiv, toL2_add, inner_add_right, hmove,
    real_inner_self_eq_norm_sq, real_inner_comm (q.toLp 2 volume) (d.toLp 2 volume)] at hibp
  change inner ℝ (q.toLp 2 volume) (d.toLp 2 volume) = _
  linarith

/-- The analytic position/derivative uncertainty inequality on Schwartz
functions, with an arbitrary position center and no normalization premise. -/
theorem norm_sq_le_two_mul_position_mul_deriv (f : SchwartzMap ℝ H) (a : ℝ) :
    ‖f.toLp 2 volume‖ ^ 2 ≤
      2 * ‖(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume‖ *
        ‖(SchwartzMap.derivCLM ℝ H f).toLp 2 volume‖ := by
  have h := real_inner_le_norm
    (-(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume)
    ((SchwartzMap.derivCLM ℝ H f).toLp 2 volume)
  rw [inner_neg_left, norm_neg, real_inner_position_deriv] at h
  nlinarith

/-- A bounded real skew operator has zero position/phase pairing. The phase
operator on Schwartz functions is the actual pointwise lift `postcompCLM K`.
The zero pairing follows by integrating pointwise skew-adjointness. -/
theorem real_inner_position_phase_eq_zero
    (f : SchwartzMap ℝ H) (a : ℝ) (K : H →L[ℝ] H)
    (hK : ∀ u v, inner ℝ (K u) v = -inner ℝ u (K v)) :
    inner ℝ
        ((SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume)
        ((SchwartzMap.postcompCLM K f).toLp 2 volume) = 0 := by
  have hg : (fun x : ℝ => x - a).HasTemperateGrowth := by fun_prop
  have hself (u : H) : inner ℝ u (K u) = 0 := by
    have h := hK u u
    rw [real_inner_comm u (K u)] at h
    linarith
  rw [real_inner_toL2]
  have hpoint (x : ℝ) :
      inner ℝ
          (SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f x)
          (SchwartzMap.postcompCLM K f x) = 0 := by
    simp only [SchwartzMap.smulLeftCLM_apply_apply hg,
      SchwartzMap.postcompCLM_apply, real_inner_smul_left, hself, mul_zero]
  simp_rw [hpoint]
  simp

/-- Centering the derivative by a real skew phase does not change its exact
position pairing. No square-minus-one or spectral assumption is needed for
this identity. -/
theorem real_inner_position_shifted_deriv
    (f : SchwartzMap ℝ H) (a b : ℝ) (K : H →L[ℝ] H)
    (hK : ∀ u v, inner ℝ (K u) v = -inner ℝ u (K v)) :
    inner ℝ
        ((SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume)
        ((SchwartzMap.derivCLM ℝ H f -
          b • SchwartzMap.postcompCLM K f).toLp 2 volume) =
      -(1 / 2 : ℝ) * ‖f.toLp 2 volume‖ ^ 2 := by
  rw [toL2_sub, toL2_smul, inner_sub_right, real_inner_smul_right,
    real_inner_position_phase_eq_zero f a K hK, mul_zero, sub_zero]
  exact real_inner_position_deriv f a

/-- Real centered position/derivative uncertainty. The derivative shift is
`D f - b K f`, where `K` is a real skew operator lifted pointwise to Schwartz
functions. Identifying this with centered physical momentum additionally
requires a rotation satisfying `K² = -I` and the chosen momentum scale. -/
theorem norm_sq_le_two_mul_position_mul_shifted_deriv
    (f : SchwartzMap ℝ H) (a b : ℝ) (K : H →L[ℝ] H)
    (hK : ∀ u v, inner ℝ (K u) v = -inner ℝ u (K v)) :
    ‖f.toLp 2 volume‖ ^ 2 ≤
      2 * ‖(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume‖ *
        ‖(SchwartzMap.derivCLM ℝ H f -
          b • SchwartzMap.postcompCLM K f).toLp 2 volume‖ := by
  have h := real_inner_le_norm
    (-(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume)
    ((SchwartzMap.derivCLM ℝ H f -
      b • SchwartzMap.postcompCLM K f).toLp 2 volume)
  rw [inner_neg_left, norm_neg, real_inner_position_shifted_deriv f a b K hK] at h
  nlinarith

/-- Squared real centered uncertainty, ready for scalar tight-frame transport. -/
theorem norm_four_le_four_mul_position_sq_mul_shifted_deriv_sq
    (f : SchwartzMap ℝ H) (a b : ℝ) (K : H →L[ℝ] H)
    (hK : ∀ u v, inner ℝ (K u) v = -inner ℝ u (K v)) :
    ‖f.toLp 2 volume‖ ^ 4 ≤
      4 * ‖(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume‖ ^ 2 *
        ‖(SchwartzMap.derivCLM ℝ H f -
          b • SchwartzMap.postcompCLM K f).toLp 2 volume‖ ^ 2 := by
  have h := norm_sq_le_two_mul_position_mul_shifted_deriv f a b K hK
  have hsq := mul_le_mul h h (sq_nonneg ‖f.toLp 2 volume‖)
    (by positivity : 0 ≤
      2 * ‖(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume‖ *
        ‖(SchwartzMap.derivCLM ℝ H f -
          b • SchwartzMap.postcompCLM K f).toLp 2 volume‖)
  nlinarith only [hsq]

end Real

/-- Squared position/derivative uncertainty, in a form suited to cancelling
one scalar tight-frame factor after transport through an analysis operator. -/
theorem norm_four_le_four_mul_position_sq_mul_deriv_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : SchwartzMap ℝ H) (a : ℝ) :
    ‖f.toLp 2 volume‖ ^ 4 ≤
      4 * ‖(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume‖ ^ 2 *
        ‖(SchwartzMap.derivCLM ℝ H f).toLp 2 volume‖ ^ 2 := by
  have h := norm_sq_le_two_mul_position_mul_deriv f a
  have hsq := mul_le_mul h h (sq_nonneg ‖f.toLp 2 volume‖)
    (by positivity : 0 ≤
      2 * ‖(SchwartzMap.smulLeftCLM H (fun x : ℝ => x - a) f).toLp 2 volume‖ *
        ‖(SchwartzMap.derivCLM ℝ H f).toLp 2 volume‖)
  nlinarith only [hsq]

end InfoGeometry.Analysis.RealSchwartzUncertainty
