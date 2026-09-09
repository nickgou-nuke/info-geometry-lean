import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Set-level regularity of the concrete completed-zeta readout

Mathlib and the existing zeta owner provide pointwise differentiability of
`riemannXi` away from `0` and `1`.  This file packages the corresponding
closed-disc statement for local contour arguments.  No removable-singularity
extension at either exceptional point is asserted.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ActualRiemannXiRegularityBridge

open Complex
open scoped Topology
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus

theorem differentiableAt_riemannXi_of_ne {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) : DifferentiableAt ℂ riemannXi s := by
  have hev : ∀ᶠ z in 𝓝 s, z ≠ 0 ∧ z ≠ 1 := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs0,
      isOpen_compl_singleton.mem_nhds hs1] with z hz0 hz1
    exact ⟨by simpa using hz0, by simpa using hz1⟩
  have heq : ∀ᶠ z in 𝓝 s, riemannXi z = entireRiemannXi z :=
    hev.mono (fun z hz => (entireRiemannXi_eq_riemannXi hz.1 hz.2).symm)
  exact differentiable_entireRiemannXi.differentiableAt.congr_of_eventuallyEq heq

theorem riemannXi_ne_zero_on_closedBall_of_one_lt_re
    (rho : ℂ) (R : ℝ)
    (hstrip : ∀ z ∈ Metric.closedBall rho R, 1 < z.re) :
    ∀ z ∈ Metric.closedBall rho R, riemannXi z ≠ 0 := by
  intro z hz
  have hRe : 1 < z.re := hstrip z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hRe
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hRe
  rw [← entireRiemannXi_eq_riemannXi hz0 hz1]
  exact entireRiemannXi_ne_zero_of_one_lt_re hRe

theorem differentiableOn_riemannXi_of_one_lt_re :
    DifferentiableOn ℂ riemannXi {z : ℂ | 1 < z.re} := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hz
  exact (differentiableAt_riemannXi_of_ne hz0 hz1).differentiableWithinAt

theorem hasDerivAt_riemannXi_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt riemannXi (deriv riemannXi s) s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  exact (differentiableAt_riemannXi_of_ne hs0 hs1).hasDerivAt

/-!
The functional equation differentiates on the regular locus.  This is the
actual derivative-level reflection law; it does not use the separate
Schwarz-reflection hypothesis.
-/

theorem riemannXi_deriv_one_sub
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv riemannXi (1 - s) = -deriv riemannXi s := by
  have hs_ref0 : 1 - s ≠ 0 := by
    intro h
    apply hs1
    exact (sub_eq_zero.mp h).symm
  have hs_ref1 : 1 - s ≠ 1 := by
    intro h
    apply hs0
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - 1 := by rw [h]
      _ = 0 := by ring
  have h_outer := (differentiableAt_riemannXi_of_ne hs_ref0 hs_ref1).hasDerivAt
  have h_inner : HasDerivAt (fun x : ℂ => 1 - x) (-1 : ℂ) s := by
    convert (hasDerivAt_const (x := s) (1 : ℂ)).sub (hasDerivAt_id s) using 1 <;>
      simp
  have h_comp := h_outer.comp s h_inner
  have h_reflected :
      HasDerivAt (fun x : ℂ => riemannXi (1 - x))
        (-deriv riemannXi (1 - s)) s := by
    convert h_comp using 1 <;> ring
  have h_reflected' : HasDerivAt riemannXi
      (-deriv riemannXi (1 - s)) s :=
    h_reflected.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun x => (riemannXi_one_sub x).symm))
  have h_deriv := h_reflected'.deriv
  have h_neg := congrArg Neg.neg h_deriv
  simpa using h_neg.symm

theorem riemannXi_logDerivative_one_sub
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv riemannXi (1 - s) / riemannXi (1 - s) =
      -(deriv riemannXi s / riemannXi s) := by
  rw [riemannXi_deriv_one_sub hs0 hs1, riemannXi_one_sub]
  ring

theorem continuousOn_riemannXi_of_one_lt_re :
    ContinuousOn riemannXi {z : ℂ | 1 < z.re} :=
  (differentiableOn_riemannXi_of_one_lt_re).continuousOn

theorem differentiableOn_riemannXi_closedBall
    (rho : ℂ) (R : ℝ)
    (h0 : ∀ z ∈ Metric.closedBall rho R, z ≠ 0)
    (h1 : ∀ z ∈ Metric.closedBall rho R, z ≠ 1) :
    DifferentiableOn ℂ riemannXi (Metric.closedBall rho R) := by
  intro z hz
  exact (differentiableAt_riemannXi_of_ne (h0 z hz) (h1 z hz)).differentiableWithinAt

theorem hasDerivAt_riemannXi_closedBall
    (rho : ℂ) (R : ℝ)
    (h0 : ∀ z ∈ Metric.closedBall rho R, z ≠ 0)
    (h1 : ∀ z ∈ Metric.closedBall rho R, z ≠ 1)
    {z : ℂ} (hz : z ∈ Metric.closedBall rho R) :
    HasDerivAt riemannXi (deriv riemannXi z) z := by
  exact (differentiableAt_riemannXi_of_ne (h0 z hz) (h1 z hz)).hasDerivAt

theorem continuousOn_riemannXi_closedBall
    (rho : ℂ) (R : ℝ)
    (h0 : ∀ z ∈ Metric.closedBall rho R, z ≠ 0)
    (h1 : ∀ z ∈ Metric.closedBall rho R, z ≠ 1) :
    ContinuousOn riemannXi (Metric.closedBall rho R) := by
  exact (differentiableOn_riemannXi_closedBall rho R h0 h1).continuousOn

theorem riemannXi_circleIntegral_eq_zero_of_closedBall_avoids_exceptions
    (rho : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (h0 : ∀ z ∈ Metric.closedBall rho R, z ≠ 0)
    (h1 : ∀ z ∈ Metric.closedBall rho R, z ≠ 1) :
    (∮ z in C(rho, R), riemannXi z) = 0 := by
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (c := rho) (f := riemannXi) (s := ∅) hR Set.countable_empty
    (differentiableOn_riemannXi_closedBall rho R h0 h1).continuousOn
    (fun z hz =>
      (differentiableOn_riemannXi_closedBall rho R h0 h1 z
        (Metric.ball_subset_closedBall hz.1)).differentiableAt
        (Metric.closedBall_mem_nhds_of_mem hz.1))

theorem riemannXi_circleIntegral_eq_zero_of_one_lt_re
    (rho : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hstrip : ∀ z ∈ Metric.closedBall rho R, 1 < z.re) :
    (∮ z in C(rho, R), riemannXi z) = 0 := by
  apply riemannXi_circleIntegral_eq_zero_of_closedBall_avoids_exceptions
    rho R hR
  · intro z hz
    intro hz0
    subst z
    have h := hstrip 0 hz
    norm_num at h
  · intro z hz
    intro hz1
    subst z
    have h := hstrip 1 hz
    norm_num at h

end InfoGeometry.Arithmetic.ActualRiemannXiRegularityBridge
