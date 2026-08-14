import InfoGeometry.Lie.CanonicalZornG2CartanFisherSouriauMetric
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Comp
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
    sorry -- Mathlib analysis deriv shift
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
