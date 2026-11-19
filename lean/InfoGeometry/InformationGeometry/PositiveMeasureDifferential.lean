/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.GaugeReduction
import InfoGeometry.InformationGeometry.ItakuraSaitoBregmanBridge
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.Finite

/-!
# Differentiating generalized KL on the finite positive cone

This file differentiates the existing `PositiveMeasure.gklTerm` and
`PositiveMeasure.generalizedKL`. Both arguments may move independently. The
second variation is a derivative of the derivative of that same divergence,
obtained by identifying its first derivative on a positive neighborhood.

The derivatives here are analytic derivatives of a real functional. They are
not algebra derivations of a noncommutative operator algebra. The final results
connect the existing generalized KL, Itakura--Saito, and projective mass split;
the reversed ratio and the weight in that connection are essential.
-/

namespace InfoGeometry.InformationGeometry.PositiveMeasureDifferential

open scoped BigOperators Topology
open InfoGeometry.PositiveMeasure
open InfoGeometry.InformationGeometry.ItakuraSaito

section Scalar

/-- The ordinary chain rule for generalized KL when its two positive entries
move independently. The hypotheses are actual native derivative propositions. -/
theorem hasDerivAt_gklTerm
    {p q : ℝ → ℝ} {u v t : ℝ}
    (hp : HasDerivAt p u t) (hq : HasDerivAt q v t)
    (hp_pos : 0 < p t) (hq_pos : 0 < q t) :
    HasDerivAt (fun s => gklTerm (p s) (q s))
      (u * Real.log (p t / q t) + v * (1 - p t / q t)) t := by
  have hp0 : p t ≠ 0 := hp_pos.ne'
  have hq0 : q t ≠ 0 := hq_pos.ne'
  have hlog := (hp.fun_div hq hq0).log (div_ne_zero hp0 hq0)
  have hraw := ((hp.mul hlog).sub hp).add hq
  apply hraw.congr_deriv
  field_simp [hp0, hq0]
  ring

private theorem hasDerivAt_affine (x u t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s * u) u t := by
  simpa only [one_mul] using ((hasDerivAt_id' t).mul_const u).const_add x

private theorem hasDerivAt_affine_firstVariation
    (p q u v : ℝ) (hp : 0 < p) (hq : 0 < q) :
    HasDerivAt
      (fun t : ℝ =>
        u * Real.log ((p + t * u) / (q + t * v)) +
          v * (1 - (p + t * u) / (q + t * v)))
      ((u - (p / q) * v) ^ 2 / p) 0 := by
  have hp0 : p ≠ 0 := hp.ne'
  have hq0 : q ≠ 0 := hq.ne'
  have hquot := (hasDerivAt_affine p u 0).fun_div
    (hasDerivAt_affine q v 0) (by simpa using hq0)
  have hlog := hquot.log (by simpa using div_ne_zero hp0 hq0)
  have hraw := (hlog.const_mul u).add ((hquot.const_sub 1).const_mul v)
  apply hraw.congr_deriv
  simp only [zero_mul, add_zero]
  field_simp [hp0, hq0]
  ring

/-- Generalized KL is weighted Itakura--Saito with the arguments reversed.
Unweighted Itakura--Saito is not generalized KL. -/
theorem gklTerm_eq_mul_isDivergence
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    gklTerm p q = p * isDivergence q p := by
  rw [gklTerm_eq p q hp.ne' hq.ne']
  unfold isDivergence
  field_simp [hp.ne']
  ring

end Scalar

section Finite

variable {α : Type*} [Fintype α]

/-- The first variation of the finite generalized KL sum along arbitrary
differentiable coordinate curves. -/
theorem hasDerivAt_sum_gklTerm
    {p q : ℝ → α → ℝ} {u v : α → ℝ} {t : ℝ}
    (hp : ∀ i, HasDerivAt (fun s => p s i) (u i) t)
    (hq : ∀ i, HasDerivAt (fun s => q s i) (v i) t)
    (hp_pos : ∀ i, 0 < p t i) (hq_pos : ∀ i, 0 < q t i) :
    HasDerivAt (fun s => ∑ i, gklTerm (p s i) (q s i))
      (∑ i, (u i * Real.log (p t i / q t i) + v i * (1 - p t i / q t i))) t := by
  classical
  exact HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => hasDerivAt_gklTerm (hp i) (hq i) (hp_pos i) (hq_pos i))

/-- The first variation directly consumes the existing bundled generalized KL. -/
theorem hasDerivAt_generalizedKL
    {μ ν : ℝ → PositiveMeasure α ℝ} {u v : α → ℝ} {t : ℝ}
    (hμ : ∀ i, HasDerivAt (fun s => μ s i) (u i) t)
    (hν : ∀ i, HasDerivAt (fun s => ν s i) (v i) t) :
    HasDerivAt (fun s => generalizedKL (μ s) (ν s))
      (∑ i, (u i * Real.log (μ t i / ν t i) + v i * (1 - μ t i / ν t i))) t := by
  simpa only [generalizedKL] using
    hasDerivAt_sum_gklTerm hμ hν (μ t).pos (ν t).pos

/-- The joint Hessian is the actual second derivative along affine lines.
Positivity is imposed at the base point; continuity provides the positive
neighborhood needed to identify the derivative of the original functional. -/
theorem hasDerivAt_deriv_sum_gklTerm_affine
    (p q u v : α → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    HasDerivAt
      (deriv (fun t : ℝ => ∑ i, gklTerm (p i + t * u i) (q i + t * v i)))
      (∑ i, (u i - (p i / q i) * v i) ^ 2 / p i) 0 := by
  classical
  have hresponse : HasDerivAt
      (fun t : ℝ => ∑ i,
        (u i * Real.log ((p i + t * u i) / (q i + t * v i)) +
          v i * (1 - (p i + t * u i) / (q i + t * v i))))
      (∑ i, (u i - (p i / q i) * v i) ^ 2 / p i) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => hasDerivAt_affine_firstVariation (p i) (q i) (u i) (v i) (hp i) (hq i))
  have hp_near : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < p i + t * u i := by
    apply Filter.eventually_all.2
    intro i
    exact continuousAt_const.eventually_lt
      (hasDerivAt_affine (p i) (u i) 0).continuousAt (by simpa using hp i)
  have hq_near : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < q i + t * v i := by
    apply Filter.eventually_all.2
    intro i
    exact continuousAt_const.eventually_lt
      (hasDerivAt_affine (q i) (v i) 0).continuousAt (by simpa using hq i)
  apply hresponse.congr_of_eventuallyEq
  filter_upwards [hp_near, hq_near] with t hpt hqt
  exact (hasDerivAt_sum_gklTerm
    (fun i => hasDerivAt_affine (p i) (u i) t)
    (fun i => hasDerivAt_affine (q i) (v i) t) hpt hqt).deriv

/-- The value of the genuine second directional derivative. -/
theorem secondDeriv_sum_gklTerm_affine
    (p q u v : α → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    deriv
      (deriv (fun t : ℝ => ∑ i, gklTerm (p i + t * u i) (q i + t * v i))) 0 =
      ∑ i, (u i - (p i / q i) * v i) ^ 2 / p i :=
  (hasDerivAt_deriv_sum_gklTerm_affine p q u v hp hq).deriv

/-- Joint affine second variations are nonnegative. -/
theorem secondDeriv_sum_gklTerm_affine_nonneg
    (p q u v : α → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    0 ≤ deriv
      (deriv (fun t : ℝ => ∑ i, gklTerm (p i + t * u i) (q i + t * v i))) 0 := by
  rw [secondDeriv_sum_gklTerm_affine p q u v hp hq]
  exact Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hp i).le)

/-- At coincident positive states the second variation is the Fisher quadratic
form of the relative tangent `u - v`, with both arguments free to move. -/
theorem hasDerivAt_deriv_sum_gklTerm_diagonal
    (p u v : α → ℝ) (hp : ∀ i, 0 < p i) :
    HasDerivAt
      (deriv (fun t : ℝ => ∑ i, gklTerm (p i + t * u i) (p i + t * v i)))
      (∑ i, (u i - v i) ^ 2 / p i) 0 := by
  apply (hasDerivAt_deriv_sum_gklTerm_affine p p u v hp hp).congr_deriv
  apply Finset.sum_congr rfl
  intro i _
  rw [div_self (hp i).ne', one_mul]

/-- Fixing the reference state recovers the usual Fisher quadratic form. -/
theorem hasDerivAt_deriv_sum_gklTerm_fixed_reference
    (p q u : α → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    HasDerivAt
      (deriv (fun t : ℝ => ∑ i, gklTerm (p i + t * u i) (q i)))
      (∑ i, (u i) ^ 2 / p i) 0 := by
  simpa only [mul_zero, add_zero, sub_zero] using
    hasDerivAt_deriv_sum_gklTerm_affine p q u (fun _ => 0) hp hq

/-- The weighted reversed-ratio identity holds for the existing bundled
generalized KL, not a newly defined divergence. -/
theorem generalizedKL_eq_weighted_isDivergence
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL μ ν = ∑ i, μ i * isDivergence (ν i) (μ i) := by
  unfold generalizedKL
  apply Finset.sum_congr rfl
  intro i _
  exact gklTerm_eq_mul_isDivergence (μ i) (ν i) (μ.pos i) (ν.pos i)

/-- The existing projective decomposition has an Itakura--Saito radial term.
The normalized shape divergence is weighted by the source mass, and the radial
Itakura--Saito term has reversed mass ratio and the same source-mass weight. -/
theorem generalizedKL_projective_isDivergence_decomposition [Nonempty α]
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL μ ν =
      Z μ * generalizedKL (normalize μ) (normalize ν) +
        Z μ * isDivergence (Z ν) (Z μ) := by
  rw [generalizedKL_projective_radial_decomposition,
    gklTerm_eq_mul_isDivergence (Z μ) (Z ν) (Z_pos μ) (Z_pos ν)]

end Finite

end InfoGeometry.InformationGeometry.PositiveMeasureDifferential
