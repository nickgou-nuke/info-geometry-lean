import InfoGeometry.Lie.CanonicalZornG2CartanFisherSouriauMetric
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import InfoGeometry.Analytic.LogSumExp

open InfoGeometry.Analytic
open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open scoped BigOperators

namespace InfoGeometry.Lie

variable {State : Type*} [Fintype State] [Nonempty State] (D : CartanSouriauDatum State)

def chargeAffineNondegenerate (D : CartanSouriauDatum State) : Prop :=
  ∀ w : Fin 2 → ℝ, w ≠ 0 →
    ∃ x y : State,
      (∑ i : Fin 2, w i * (D.momentMap x i - D.momentMap y i)) ≠ 0

theorem betaLine_add (beta v : Fin 2 → ℝ) (t s : ℝ) :
    betaLine beta v (t + s) = betaLine (betaLine beta v t) v s := by
  ext i
  unfold betaLine
  ring


theorem deriv_shift_zero {f : ℝ → ℝ} (t : ℝ) (hf : DifferentiableAt ℝ f t) :
    deriv (fun s => f (t + s)) 0 = deriv f t := by
  have hd1 : HasDerivAt f (deriv f t) (t + 0) := by
    rw [add_zero]
    exact hf.hasDerivAt
  have hd2 : HasDerivAt (fun s => t + s) 1 0 := by
    apply HasDerivAt.const_add
    exact hasDerivAt_id 0
  have hc := HasDerivAt.comp 0 hd1 hd2
  rw [mul_one] at hc
  exact hc.deriv

theorem deriv_shift {f : ℝ → ℝ} (t : ℝ) (s : ℝ) (hf : DifferentiableAt ℝ f (t + s)) :
    deriv (fun s' => f (t + s')) s = deriv f (t + s) := by
  have hd1 : HasDerivAt f (deriv f (t + s)) (t + s) := hf.hasDerivAt
  have hd2 : HasDerivAt (fun s' => t + s') 1 s := by
    apply HasDerivAt.const_add
    exact hasDerivAt_id s
  have hc := HasDerivAt.comp s hd1 hd2
  rw [mul_one] at hc
  exact hc.deriv

theorem second_deriv_shift {f : ℝ → ℝ} (t : ℝ)
    (hf : ContDiff ℝ 2 f) :
    deriv^[2] f t = deriv (fun s => deriv (fun s' => f (t + s')) s) 0 := by
  change deriv (deriv f) t = deriv (fun s => deriv (fun s' => f (t + s')) s) 0
  have h_inner (s : ℝ) : deriv (fun s' => f (t + s')) s = deriv f (t + s) := by
    apply deriv_shift
    have h1 := hf.differentiable (by norm_num)
    exact h1 (t + s)
  have h_outer : (fun s => deriv (fun s' => f (t + s')) s) = (fun s => deriv f (t + s)) := by
    ext s
    exact h_inner s
  rw [h_outer]
  apply (deriv_shift_zero t _).symm
  have hd := hf.differentiable_deriv_two
  exact hd t

theorem souriauMassieu_strictlyConvex_along_lines
    (h_nondeg : chargeAffineNondegenerate D)
    (beta v : Fin 2 → ℝ) (hv : v ≠ 0) :
    StrictConvexOn ℝ Set.univ (fun t => souriauMassieu D (betaLine beta v t)) := by
  let w : State → ℝ := fun x => Real.exp (-(∑ j : Fin 2, beta j * D.momentMap x j))
  let a : State → ℝ := fun x => -(∑ j : Fin 2, v j * D.momentMap x j)
  have hline : (fun t => souriauMassieu D (betaLine beta v t)) = (fun t => logSumExp w a t) := by
    ext t
    unfold souriauMassieu betaLine logSumExp logSumExpPartition realGibbsPartition realGibbsKernel realPairingEnergy w a
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [← Real.exp_add]
    congr 1
    simp only [Fin.sum_univ_two]
    ring
  rw [hline]
  have hw : ∀ x, 0 < w x := fun x => Real.exp_pos _
  have hf_contDiff : ContDiff ℝ 2 (logSumExp w a) := logSumExp_contDiff w a hw
  have hf_cont : ContinuousOn (logSumExp w a) Set.univ := hf_contDiff.continuous.continuousOn
  apply strictConvexOn_of_deriv2_pos' convex_univ hf_cont
  intro t _
  have hs2 : deriv^[2] (logSumExp w a) t = deriv (fun s => deriv (fun s' => logSumExp w a (t + s')) s) 0 := by
    let f := logSumExp w a
    have hfd : DifferentiableAt ℝ (deriv f) t := by
      have hfr := (hf_contDiff.contDiffAt (x := t)).fderiv_right
        (m := (1 : WithTop ℕ∞)) (n := (2 : WithTop ℕ∞)) (by norm_num)
      have hfrapp := hfr.clm_apply
        (contDiffAt_const (x := t) (n := (1 : WithTop ℕ∞)) (c := (1 : ℝ)))
      have hfrd := hfrapp.differentiableAt
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
      convert hfrd using 1
    have hg : HasDerivAt (deriv f) (deriv (deriv f) t) t := hfd.hasDerivAt
    have hg0 : HasDerivAt (deriv f) (deriv (deriv f) t) (t + 0) := by
      simpa using hg
    have hs := hg0.comp_const_add t 0
    have hsd : deriv (fun s => deriv f (t + s)) 0 = deriv (deriv f) t := hs.deriv
    have hinner :
        (fun s => deriv (fun s' => f (t + s')) s) =
          (fun s => deriv f (t + s)) := by
      funext s
      exact deriv_comp_const_add f t s
    rw [hinner]
    simpa [f, Function.iterate_succ_apply, Function.iterate_zero_apply] using hsd.symm
  rw [hs2]
  have hline_ts : (fun s' => logSumExp w a (t + s')) = (fun s' => souriauMassieu D (betaLine (betaLine beta v t) v s')) := by
    ext s'
    have h_eval : logSumExp w a (t + s') = souriauMassieu D (betaLine beta v (t + s')) := by
      have h1 : souriauMassieu D (betaLine beta v (t + s')) = logSumExp w a (t + s') := by
        have h1_eq := congr_fun hline (t + s')
        exact h1_eq
      exact h1.symm
    rw [h_eval]
    rw [betaLine_add]
  rw [hline_ts]
  have h_deriv2 := souriauMassieu_directionalSecondDeriv_eq_fisherSouriauQuadratic D (betaLine beta v t) v
  rw [h_deriv2]
  exact fisherSouriauQuadratic_pos_of_charge_separates D (betaLine beta v t) v hv h_nondeg

theorem souriauMassieu_strictConvex
    (h_nondeg : chargeAffineNondegenerate D) :
    StrictConvexOn ℝ Set.univ (souriauMassieu D) := by
  constructor
  · exact convex_univ
  · intro x hx y hy hxy a b ha hb hab
    let v : Fin 2 → ℝ := x - y
    have hv : v ≠ 0 := sub_ne_zero.mpr hxy
    have h_line_convex := souriauMassieu_strictlyConvex_along_lines D h_nondeg y v hv
    have h_line_convex_def := h_line_convex.2 (Set.mem_univ 1) (Set.mem_univ 0) (by norm_num) ha hb hab
    have hab_mid : betaLine y v a = a • x + b • y := by
      ext i
      unfold betaLine v
      have hb_eq : b = 1 - a := eq_sub_of_add_eq' hab
      rw [hb_eq]
      dsimp
      ring
    have hab_t : a • (1 : ℝ) + b • (0 : ℝ) = a := by
      simp
    rw [hab_t] at h_line_convex_def
    have hf0 : souriauMassieu D (betaLine y v 0) = souriauMassieu D y := by
      congr 1; ext i; unfold betaLine; ring
    have hf1 : souriauMassieu D (betaLine y v 1) = souriauMassieu D x := by
      congr 1; ext i; unfold betaLine v; dsimp; ring
    have hfa : souriauMassieu D (betaLine y v a) = souriauMassieu D (a • x + b • y) := by rw [hab_mid]
    change souriauMassieu D (betaLine y v a) < a • souriauMassieu D (betaLine y v 1) + b • souriauMassieu D (betaLine y v 0) at h_line_convex_def
    rw [hf0, hf1, hfa] at h_line_convex_def
    exact h_line_convex_def

end InfoGeometry.Lie
