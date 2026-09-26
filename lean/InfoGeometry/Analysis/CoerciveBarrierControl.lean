import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic

/-!
# The quantitative estimate required for singular-locus avoidance

An energy balance `E' = production - dissipation`, with dissipation dominating
production, bounds `E` on a finite interval. If `-log d ≤ E` on the positive
domain, the singular-locus distance has the explicit lower bound `exp(-E(0))`.
These are proved estimates, with the dynamical and coercivity hypotheses
visible. No topological index supplies those hypotheses, and no
Navier--Stokes continuation theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Analysis.CoerciveBarrierControl

open Set

open Filter in
/-- A strictly positive uniform lower bound excludes a zero limit. -/
theorem not_tendsto_zero_of_separation {α : Type*} {l : Filter α} [l.NeBot]
    {d : α → ℝ} {ε : ℝ} (hε : 0 < ε) (hd : ∀ᶠ x in l, ε ≤ d x) :
    ¬ Tendsto d l (nhds 0) := by
  intro hlim
  exact (not_le_of_gt hε) (ge_of_tendsto hlim hd)

theorem exp_neg_le_of_log_barrier_le {d E : ℝ}
    (hd : 0 < d) (h : -Real.log d ≤ E) : Real.exp (-E) ≤ d := by
  calc
    Real.exp (-E) ≤ Real.exp (Real.log d) := Real.exp_le_exp.mpr (by linarith)
    _ = d := Real.exp_log hd

/-- The supplied production/dissipation law yields an actual energy bound. -/
theorem energy_le_initial (E production dissipation : ℝ → ℝ) {T t : ℝ}
    (hE : ContinuousOn E (Ico 0 T))
    (hderiv : ∀ s ∈ Ico 0 T, HasDerivAt E (production s - dissipation s) s)
    (hdom : ∀ s ∈ Ico 0 T, production s ≤ dissipation s)
    (ht : t ∈ Ico 0 T) : E t ≤ E 0 := by
  have hanti : AntitoneOn E (Ico 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico 0 T) hE
    · intro s hs
      exact (hderiv s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hderiv s (interior_subset hs)).deriv]
      exact sub_nonpos.mpr (hdom s (interior_subset hs))
  exact hanti ⟨le_rfl, lt_of_le_of_lt ht.1 ht.2⟩ ht ht.1

/-- A log-coercive energy balance uniformly separates the trajectory from `d=0`. -/
theorem uniform_separation (E production dissipation d : ℝ → ℝ) {T : ℝ}
    (hE : ContinuousOn E (Ico 0 T))
    (hderiv : ∀ s ∈ Ico 0 T, HasDerivAt E (production s - dissipation s) s)
    (hdom : ∀ s ∈ Ico 0 T, production s ≤ dissipation s)
    (hd : ∀ s ∈ Ico 0 T, 0 < d s)
    (hcoercive : ∀ s ∈ Ico 0 T, -Real.log (d s) ≤ E s) :
    0 < Real.exp (-E 0) ∧ ∀ t ∈ Ico 0 T, Real.exp (-E 0) ≤ d t := by
  refine ⟨Real.exp_pos _, fun t ht => ?_⟩
  exact exp_neg_le_of_log_barrier_le (hd t ht)
    ((hcoercive t ht).trans (energy_le_initial E production dissipation hE hderiv hdom ht))

/-- A positive observable also needs its own coercive estimate. -/
theorem observable_le_of_coercive_energy (E production dissipation G : ℝ → ℝ)
    {T t c : ℝ} (hc : 0 < c)
    (hE : ContinuousOn E (Ico 0 T))
    (hderiv : ∀ s ∈ Ico 0 T, HasDerivAt E (production s - dissipation s) s)
    (hdom : ∀ s ∈ Ico 0 T, production s ≤ dissipation s)
    (hcoercive : ∀ s ∈ Ico 0 T, c * G s ≤ E s)
    (ht : t ∈ Ico 0 T) : G t ≤ E 0 / c := by
  apply (le_div_iff₀ hc).mpr
  simpa [mul_comm] using
    (hcoercive t ht).trans (energy_le_initial E production dissipation hE hderiv hdom ht)

/-- Weak-value quotients are bounded only when both numerator and denominator are controlled. -/
theorem quotient_norm_le {n q : ℂ} {C ε : ℝ}
    (hε : 0 < ε) (hn : ‖n‖ ≤ C) (hq : ε ≤ ‖q‖) :
    ‖n / q‖ ≤ C / ε := by
  rw [norm_div]
  exact div_le_div₀ ((norm_nonneg _).trans hn) hn hε hq

/-- A directional quotient derivative requires numerator and derivative bounds
as well as denominator separation. This is a one-parameter calculus theorem. -/
theorem quotient_derivative_norm_le
    {n q : ℝ → ℂ} {t : ℝ} {n' q' : ℂ} {Cn Cn' Cq' ε : ℝ}
    (hn : HasDerivAt n n' t) (hq : HasDerivAt q q' t)
    (hε : 0 < ε) (hsep : ε ≤ ‖q t‖)
    (hnum : ‖n t‖ ≤ Cn) (hnum' : ‖n'‖ ≤ Cn') (hden' : ‖q'‖ ≤ Cq') :
    ‖deriv (fun s => n s / q s) t‖ ≤ Cn' / ε + Cn * Cq' / ε ^ 2 := by
  have hq0 : q t ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hε hsep)
  have heq : deriv (fun s => n s / q s) t =
      n' / q t - n t * q' / (q t) ^ 2 := by
    change deriv (n / q) t = _
    rw [(hn.div hq hq0).deriv]
    field_simp
  rw [heq]
  apply (norm_sub_le _ _).trans
  apply add_le_add (quotient_norm_le hε hnum' hsep)
  apply quotient_norm_le (sq_pos_of_pos hε)
  · rw [norm_mul]
    exact mul_le_mul hnum hden' (norm_nonneg _) ((norm_nonneg _).trans hnum)
  · rw [norm_pow]
    exact pow_le_pow_left₀ hε.le hsep 2

end InfoGeometry.Analysis.CoerciveBarrierControl
