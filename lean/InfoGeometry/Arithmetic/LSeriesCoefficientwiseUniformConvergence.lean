/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Portions adapted from Māris Ozols' RiemannMasullo project, Apache-2.0,
revision e7476c3874f31498aa822bf8eee47e4b52170230.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform convergence for coefficientwise-stabilizing L-series

If a family of coefficient sequences stabilizes at every index and its absolute
Dirichlet sums are uniformly bounded at a real exponent `r`, then the associated
L-series converge uniformly on every closed half-plane `a ≤ re(s)` with `r < a`.
The theorem is about analytic L-series of coefficient sequences; it asserts no
functional equation, continuation, or arithmetic Euler product.

The proof follows `external_refs/riemann-masullo/RiemannMasullo/ForMathlib/NumberTheory/LSeries/Convergence.lean`
(Apache-2.0, Māris Ozols, revision
`e7476c3874f31498aa822bf8eee47e4b52170230`) and is checked against this
checkout's pinned Mathlib.
-/

public section

open Filter Set
open scoped Topology

namespace InfoGeometry.Arithmetic.LSeriesCoefficientwiseUniformConvergence

/-- Moving from a real exponent `r` to a larger real exponent `a` suppresses each
nonzero Dirichlet term by the factor `n^(r-a)`. -/
private theorem norm_LSeries_term_shift (f : ℕ → ℂ) (r a : ℝ) (n : ℕ) :
    ‖LSeries.term f (a : ℂ) n‖ = (n : ℝ) ^ (r - a) * ‖LSeries.term f (r : ℂ) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  simp only [LSeries.norm_term_eq, hn, ite_false, Complex.ofReal_re, Real.rpow_sub hn']
  field_simp [(Real.rpow_pos_of_pos hn' r).ne', (Real.rpow_pos_of_pos hn' a).ne']

/-- Coefficientwise stabilization and a uniform absolute Dirichlet bound at a real
exponent imply uniform convergence on closed half-planes strictly to its right. -/
theorem tendstoUniformlyOn_LSeries_of_eventuallyEq {ι : Type*} {l : Filter ι}
    (f : ι → ℕ → ℂ) (g : ℕ → ℂ) {r a C : ℝ} (hra : r < a) (hC : 0 ≤ C)
    (hf : ∀ i, LSeriesSummable (f i) (r : ℂ)) (hg : LSeriesSummable g (r : ℂ))
    (hb : ∀ i, ∑' n, ‖LSeries.term (f i) (r : ℂ) n‖ ≤ C)
    (he : ∀ n, ∀ᶠ i in l, f i n = g n) :
    TendstoUniformlyOn (fun i s ↦ LSeries (f i) s) (LSeries g) l {s : ℂ | a ≤ s.re} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let D := ∑' n, ‖LSeries.term g (r : ℂ) n‖
  have hD : 0 ≤ D := tsum_nonneg fun _ ↦ norm_nonneg _
  let δ := ε / (D + C + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (r - a)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hra)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_lt_const hδ)
  filter_upwards [(Filter.eventually_all_finset (Finset.range N)).mpr (fun n _ ↦ he n)] with i hi
  intro s hs
  have hrs : (r : ℂ).re ≤ s.re := hra.le.trans hs
  rw [dist_eq_norm, ← LSeries_sub (hg.of_re_le_re hrs) ((hf i).of_re_le_re hrs)]
  have hmajor := (hg.norm.hasSum.add (hf i).norm.hasSum).mul_left δ
  have hle : ‖LSeries (g - f i) s‖ ≤
      δ * (D + ∑' n, ‖LSeries.term (f i) (r : ℂ) n‖) := by
    apply tsum_of_norm_bounded hmajor
    intro n
    by_cases hn : n < N
    · have hn' := hi n (Finset.mem_range.mpr hn)
      simp [LSeries.term, hn', Pi.sub_apply]
      positivity
    · calc
        ‖LSeries.term (g - f i) s n‖ ≤ ‖LSeries.term (g - f i) (a : ℂ) n‖ :=
          LSeries.norm_term_le_of_re_le_re _ hs n
        _ = (n : ℝ) ^ (r - a) * ‖LSeries.term (g - f i) (r : ℂ) n‖ :=
          norm_LSeries_term_shift _ _ _ _
        _ ≤ δ * (‖LSeries.term g (r : ℂ) n‖ +
            ‖LSeries.term (f i) (r : ℂ) n‖) := by
          rw [LSeries.term_sub_apply]
          exact mul_le_mul (hN n (Nat.le_of_not_gt hn)).le (norm_sub_le _ _)
            (norm_nonneg _) hδ.le
  refine lt_of_le_of_lt
    (hle.trans (mul_le_mul_of_nonneg_left (add_le_add_right (hb i) D) hδ.le)) ?_
  calc
    δ * (D + C) < δ * (D + C + 1) :=
      mul_lt_mul_of_pos_left (by linarith) hδ
    _ = ε := div_mul_cancel₀ _ (by linarith)

end InfoGeometry.Arithmetic.LSeriesCoefficientwiseUniformConvergence
