import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic
import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge

/-!
# Entire completed Riemann-xi realization

Mathlib provides the pole-removed entire function `completedRiemannZeta₀`.
Multiplying its correction identity by `s * (s - 1)` gives the entire
completed xi representative

  `1 / 2 * (s * (s - 1) * completedRiemannZeta₀ s + 1)`.

This owner distinguishes that genuine entire representative from the existing
`riemannXi` readout, which is definitionally expressed through the meromorphic
completed zeta and is only identified with it away from `0` and `1`.
No zero-location or Riemann-hypothesis claim is made.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge

/-- Entire representative of the completed Riemann xi function. -/
def entireRiemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta₀ s + 1)

theorem differentiable_entireRiemannXi :
    Differentiable ℂ entireRiemannXi := by
  have hΛ : Differentiable ℂ completedRiemannZeta₀ :=
    differentiable_completedZeta₀
  unfold entireRiemannXi
  have hpoly : Differentiable ℂ (fun s : ℂ => s * (s - 1)) := by
    fun_prop
  have hprod : Differentiable ℂ
      (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s) := by
    exact hpoly.mul hΛ
  exact (hprod.add (differentiable_const (1 : ℂ))).const_mul (1 / 2 : ℂ)

/-! `Differentiable` is enough here to obtain the local analytic structure on
the whole plane.  The analytic API then transports regularity to the
derivative, which is needed by downstream logarithmic-form owners. -/

theorem analyticOnNhd_entireRiemannXi :
    AnalyticOnNhd ℂ entireRiemannXi Set.univ := by
  have hΛ : AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ := by
    apply (analyticOn_univ).mp
    exact differentiable_completedZeta₀.differentiableOn.analyticOn isOpen_univ
  have hid : AnalyticOnNhd ℂ (fun s : ℂ => s) Set.univ := analyticOnNhd_id
  have hone : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) Set.univ :=
    analyticOnNhd_const
  have hpoly : AnalyticOnNhd ℂ
      (fun s : ℂ => s * (s - 1)) Set.univ := by
    exact hid.mul (hid.sub hone)
  have hprod : AnalyticOnNhd ℂ
      (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s) Set.univ := by
    exact hpoly.mul hΛ
  have hsum : AnalyticOnNhd ℂ
      (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) Set.univ := by
    exact hprod.add hone
  unfold entireRiemannXi
  exact hsum.const_smul (R := ℂ)

theorem analyticOnNhd_deriv_entireRiemannXi :
    AnalyticOnNhd ℂ (deriv entireRiemannXi) Set.univ :=
  analyticOnNhd_entireRiemannXi.deriv

theorem differentiable_deriv_entireRiemannXi :
    Differentiable ℂ (deriv entireRiemannXi) := by
  apply (differentiableOn_univ).mp
  exact analyticOnNhd_deriv_entireRiemannXi.differentiableOn

theorem entireRiemannXi_one_sub (s : ℂ) :
    entireRiemannXi (1 - s) = entireRiemannXi s := by
  unfold entireRiemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-! The entire representative has a derivative-level reflection law with no
exceptional-point hypotheses.  This is the regularized counterpart of the
away-from-poles theorem in `ActualRiemannXiRegularityBridge`. -/

theorem deriv_entireRiemannXi_one_sub (s : ℂ) :
    deriv entireRiemannXi (1 - s) = -deriv entireRiemannXi s := by
  have h_outer := (differentiable_entireRiemannXi (1 - s)).hasDerivAt
  have h_inner : HasDerivAt (fun x : ℂ => 1 - x) (-1 : ℂ) s := by
    convert (hasDerivAt_const (x := s) (1 : ℂ)).sub (hasDerivAt_id s) using 1 <;>
      simp
  have h_comp := h_outer.comp s h_inner
  have h_reflected : HasDerivAt (fun x : ℂ => entireRiemannXi (1 - x))
      (-deriv entireRiemannXi (1 - s)) s := by
    convert h_comp using 1 <;> ring
  have h_reflected' : HasDerivAt entireRiemannXi
      (-deriv entireRiemannXi (1 - s)) s :=
    h_reflected.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun x => (entireRiemannXi_one_sub x).symm))
  have h_deriv := h_reflected'.deriv
  have h_neg := congrArg Neg.neg h_deriv
  simpa using h_neg.symm

theorem entireRiemannXi_eq_riemannXi
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireRiemannXi s = riemannXi s := by
  unfold entireRiemannXi riemannXi
  rw [completedRiemannZeta_eq]
  have h1 : 1 - s ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hs1)
  field_simp [hs0, hs1, h1]
  ring

theorem entireRiemannXi_eq_riemannXi_on_regular_locus
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = entireRiemannXi s :=
  (entireRiemannXi_eq_riemannXi hs0 hs1).symm

/-! On the critical line the regularized entire representative is real.  The
proof uses only the concrete Schwarz symmetry of `riemannXi` and the regular
identification away from `0` and `1`. -/

theorem entireRiemannXi_criticalLine_conj (t : ℝ) :
    star (entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) =
      entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
  have hstar : star s = 1 - s := by
    apply Complex.ext <;> simp [s] <;> ring
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
  have hriem := riemannXi_conj_of_completed actualCompletedRiemannZetaSchwarz s
  calc
    star (entireRiemannXi s) = star (riemannXi s) := by
      rw [entireRiemannXi_eq_riemannXi hs0 hs1]
    _ = riemannXi (star s) := hriem.symm
    _ = riemannXi (1 - s) := by rw [hstar]
    _ = entireRiemannXi (1 - s) :=
      (entireRiemannXi_eq_riemannXi hs_ref0 hs_ref1).symm
    _ = entireRiemannXi s := entireRiemannXi_one_sub s

theorem entireRiemannXi_criticalLine_even (t : ℝ) :
    entireRiemannXi ((1 / 2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) =
      entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
  calc
    entireRiemannXi ((1 / 2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) =
        entireRiemannXi (1 - ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) := by
      congr 1
      push_cast
      ring
    _ = entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) :=
      entireRiemannXi_one_sub _

theorem deriv_entireRiemannXi_criticalLine_odd (t : ℝ) :
    deriv entireRiemannXi ((1 / 2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) =
      -deriv entireRiemannXi ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
  have hcoord :
      (1 / 2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ) =
        1 - ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
    push_cast
    ring
  rw [hcoord]
  exact deriv_entireRiemannXi_one_sub _

end ActualRiemannXiEntireBridge
