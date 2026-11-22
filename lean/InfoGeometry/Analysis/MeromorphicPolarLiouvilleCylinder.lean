/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# InfoGeometry.Analysis.MeromorphicPolarLiouvilleCylinder

Ported to Mathlib `v4.34.1` from `mccorvie/riemann-masullo` (Apache-2.0, upstream
commit `b967ac4`):
- `RiemannMasullo/ForMathlib/Analysis/Meromorphic/PrincipalPart.lean`
- `RiemannMasullo/ForMathlib/Analysis/Complex/Liouville.lean`
- `RiemannMasullo/ForMathlib/Analysis/Complex/CoveringMap.lean`

Provides:
- `analyticAt_exists_polar_expansion` and `meromorphicAt_exists_polar_expansion`:
  finite Laurent principal-part + analytic germ decomposition on a punctured
  neighborhood;
- `exists_eq_const_mul_exp_of_norm_add_mul_I`: Liouville rigidity for zero-free
  entire functions with vertically invariant modulus;
- `exists_complexPowerCylinder`: homeomorphic quotient presentation
  `(ℂ ⧸ ℤ · (2πi / log q)) ≃ₜ ℂˣ` realizing `s ↦ b * q ^ (-s)`.
-/

noncomputable section

open Filter Function Set
open scoped Topology BigOperators

namespace InfoGeometry.Analysis.MeromorphicPolarLiouvilleCylinder

/-- Dividing an analytic germ by `(z - ρ) ^ n` decomposes on `z ≠ ρ` into an
analytic germ `H` plus a finite sum of negative powers `c k * (z - ρ) ^ (-k - 1)`. -/
theorem analyticAt_exists_polar_expansion {a : ℂ → ℂ} {ρ : ℂ}
    (ha : AnalyticAt ℂ a ρ) (n : ℕ) :
    ∃ (H : ℂ → ℂ) (c : ℕ → ℂ), AnalyticAt ℂ H ρ ∧
      ∀ z ≠ ρ, a z * (z - ρ) ^ (-(n : ℤ)) =
        H z + ∑ k ∈ Finset.range n, c k * (z - ρ) ^ (-(k : ℤ) - 1) := by
  induction n generalizing a with
  | zero => exact ⟨a, 0, ha, by simp⟩
  | succ n ih =>
    have ha_ev : ∀ᶠ z in 𝓝 ρ, AnalyticAt ℂ a z := ha.eventually_analyticAt
    obtain ⟨r, hr, hsub⟩ := Metric.eventually_nhds_iff_ball.mp ha_ev
    have hdiff : DifferentiableOn ℂ a (Metric.ball ρ r) :=
      fun z hz ↦ (hsub z hz).differentiableAt.differentiableWithinAt
    have hdslope : DifferentiableOn ℂ (dslope a ρ) (Metric.ball ρ r) :=
      (Complex.differentiableOn_dslope (Metric.ball_mem_nhds ρ hr)).mpr hdiff
    have hdslope_an : AnalyticAt ℂ (dslope a ρ) ρ :=
      (hdslope.analyticOnNhd Metric.isOpen_ball) ρ (Metric.mem_ball_self hr)
    obtain ⟨H, c, hH, he⟩ := ih hdslope_an
    refine ⟨H, Function.update c n (a ρ), hH, fun z hz ↦ ?_⟩
    have hn : ∀ k ∈ Finset.range n, Function.update c n (a ρ) k = c k :=
      fun k hk ↦ Function.update_of_ne (Finset.mem_range.mp hk).ne _ _
    have hsum :
        ∑ k ∈ Finset.range n, Function.update c n (a ρ) k * (z - ρ) ^ (-(k : ℤ) - 1) =
          ∑ k ∈ Finset.range n, c k * (z - ρ) ^ (-(k : ℤ) - 1) :=
      Finset.sum_congr rfl fun k hk ↦ by rw [hn k hk]
    have hsplit : a z = dslope a ρ z * (z - ρ) + a ρ := by
      rw [mul_comm, ← smul_eq_mul, sub_smul_dslope a ρ z, sub_add_cancel]
    have hpow :
        (z - ρ) * (z - ρ) ^ (-(↑(n + 1) : ℤ)) = (z - ρ) ^ (-(n : ℤ)) := by
      conv_lhs => enter [1]; rw [← zpow_one (z - ρ)]
      rw [← zpow_add₀ (sub_ne_zero.mpr hz)]
      congr 1
      omega
    rw [Finset.sum_range_succ, hsum, Function.update_self, ← add_assoc, ← he z hz]
    push_cast
    rw [show -(n : ℤ) - 1 = -((n : ℤ) + 1) by omega]
    conv_lhs => enter [1]; rw [hsplit]
    rw [add_mul, mul_assoc]
    push_cast at hpow
    rw [hpow]

/-- A meromorphic germ agrees on a punctured neighborhood with an analytic
germ plus a finite sum of negative powers of the displacement from its center.
The term indexed by `k` has exponent `-k - 1`. -/
theorem meromorphicAt_exists_polar_expansion {f : ℂ → ℂ} {ρ : ℂ}
    (hf : MeromorphicAt f ρ) :
    ∃ (n : ℕ) (H : ℂ → ℂ) (c : ℕ → ℂ), AnalyticAt ℂ H ρ ∧
      f =ᶠ[𝓝[≠] ρ] (fun z ↦ H z + ∑ k ∈ Finset.range n, c k * (z - ρ) ^ (-(k : ℤ) - 1)) := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨H, c, hH, he⟩ := analyticAt_exists_polar_expansion hn n
  refine ⟨n, H, c, hH, ?_⟩
  filter_upwards [self_mem_nhdsWithin (a := ρ) (s := ({ρ}ᶜ : Set ℂ))] with z hz
  rw [← he z (mem_compl_singleton_iff.mp hz), smul_eq_mul, zpow_neg, zpow_natCast,
    mul_comm ((z - ρ) ^ n) (f z), mul_assoc, mul_inv_cancel₀, mul_one]
  exact pow_ne_zero _ (sub_ne_zero.mpr (mem_compl_singleton_iff.mp hz))

/-- An entire function without zeros whose modulus is invariant under imaginary translations
is a nonzero constant times an exponential with real exponent coefficient. -/
theorem exists_eq_const_mul_exp_of_norm_add_mul_I {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf₀ : ∀ z, f z ≠ 0)
    (hNorm : ∀ z (t : ℝ), ‖f (z + (t : ℂ) * Complex.I)‖ = ‖f z‖) :
    ∃ r : ℝ, ∀ z, f z = f 0 * Complex.exp ((r : ℂ) * z) := by
  have hShift (t : ℝ) (z : ℂ) :
      f (z + (t : ℂ) * Complex.I) * f 0 = f z * f ((t : ℂ) * Complex.I) := by
    let g (w : ℂ) := f (w + (t : ℂ) * Complex.I) / f w
    have hg : Differentiable ℂ g :=
      (hf.comp (differentiable_id.add_const _)).div hf hf₀
    have hBound : Bornology.IsBounded (range g) := by
      refine isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩
      rintro _ ⟨w, rfl⟩
      change ‖f (w + (t : ℂ) * Complex.I) / f w‖ ≤ 1
      rw [norm_div, hNorm, div_self (norm_ne_zero_iff.mpr (hf₀ w))]
    have h := hg.apply_eq_apply_of_bounded hBound z 0
    simpa only [g, zero_add, div_eq_div_iff (hf₀ z) (hf₀ 0),
      mul_comm (f ((t : ℂ) * Complex.I))] using h
  have hAlong (z : ℂ) :
      (fun w ↦ f (z + w) * f 0) = fun w ↦ f z * f w := by
    apply AnalyticOnNhd.eq_of_frequently_eq (z₀ := 0)
    · exact fun w _ ↦ (hf.analyticAt (z + w)).comp
        (analyticAt_const.add analyticAt_id) |>.mul analyticAt_const
    · exact fun w _ ↦ analyticAt_const.mul (hf.analyticAt w)
    have ht : Tendsto (fun t : ℝ ↦ (t : ℂ) * Complex.I) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun t : ℝ ↦ (t : ℂ) * Complex.I) := by fun_prop
        simpa only [Complex.ofReal_zero, zero_mul] using
          (hc.continuousAt.continuousWithinAt (x := (0 : ℝ)) (s := {0}ᶜ)).tendsto
      · filter_upwards [self_mem_nhdsWithin (s := ({0} : Set ℝ)ᶜ) (a := 0)] with t ht
        simpa using ht
    exact ht.frequently (Frequently.of_forall fun t ↦ hShift t z)
  let a := deriv f 0 / f 0
  have hDeriv (z : ℂ) : deriv f z = a * f z := by
    have hz := (hf.differentiableAt (x := z)).hasDerivAt
    have hLeft : HasDerivAt (fun w ↦ f (z + w) * f 0) (deriv f z * f 0) 0 := by
      have hc : HasDerivAt (fun w : ℂ ↦ z + w) 1 0 := (hasDerivAt_id 0).const_add z
      simpa only [Function.comp_apply, id_eq, add_zero, mul_one] using
        ((show HasDerivAt f (deriv f z) (z + 0) by simpa only [add_zero] using hz).comp 0
          hc).mul_const (f 0)
    rw [hAlong z] at hLeft
    have h := hLeft.unique ((hf.differentiableAt (x := 0)).hasDerivAt.const_mul (f z))
    dsimp only [a]
    rw [div_mul_eq_mul_div, eq_div_iff (hf₀ 0), mul_comm (deriv f 0)]
    exact h
  let g (z : ℂ) := f z * Complex.exp (-a * z)
  have hg (z : ℂ) : HasDerivAt g 0 z := by
    have he := ((hasDerivAt_id z).const_mul (-a)).cexp
    simp only [id_eq, mul_one] at he
    convert (hf.differentiableAt.hasDerivAt.mul he : HasDerivAt g _ z) using 1
    rw [hDeriv]
    ring
  have hExp (z : ℂ) : f z = f 0 * Complex.exp (a * z) := by
    have h := is_const_of_deriv_eq_zero (fun w ↦ (hg w).differentiableAt)
      (fun w ↦ (hg w).deriv) z 0
    have he : Complex.exp (-a * z) * Complex.exp (a * z) = 1 := by
      rw [← Complex.exp_add, show -a * z + a * z = 0 by ring, Complex.exp_zero]
    simpa only [g, mul_zero, Complex.exp_zero, mul_one, mul_assoc, he] using
      congrArg (· * Complex.exp (a * z)) h
  have hI : ‖f Complex.I‖ = ‖f 0‖ := by simpa using hNorm 0 1
  rw [hExp Complex.I, norm_mul, Complex.norm_exp] at hI
  have hIm : a.im = 0 := by
    have h := mul_left_cancel₀ (norm_ne_zero_iff.mpr (hf₀ 0)) (hI.trans (mul_one _).symm)
    have hh : Real.exp ((a * Complex.I).re) = Real.exp 0 := h.trans Real.exp_zero.symm
    simpa [Complex.mul_re] using Real.exp_injective hh
  refine ⟨a.re, ?_⟩
  have hReal : (a.re : ℂ) = a := by
    apply Complex.ext <;> simp [hIm]
  simpa only [hReal] using hExp

/-- Exponentiating with base greater than one identifies the period cylinder with the
nonzero complex numbers, also after multiplication by a fixed unit. -/
theorem exists_complexPowerCylinder (q : ℝ) (hq : 1 < q) (b : ℂˣ) :
    let P := AddSubgroup.zmultiples (2 * (Real.pi : ℂ) * Complex.I / (Real.log q : ℂ))
    ∃ e : (ℂ ⧸ P) ≃ₜ ℂˣ, ∀ s : ℂ, (e (QuotientAddGroup.mk s) : ℂ) = b * (q : ℂ) ^ (-s) := by
  let L : ℂ := Real.log q
  have hL : L ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  let T : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let P := AddSubgroup.zmultiples (T / L)
  let expNonzero (z : ℂ) : {w : ℂ // w ≠ 0} := ⟨Complex.exp z, z.exp_ne_zero⟩
  let expUnit : ℂ → ℂˣ := (unitsHomeomorphNeZero (G₀ := ℂ)).symm ∘ expNonzero
  have hval (z : ℂ) : (expUnit z : ℂ) = Complex.exp z :=
    congrArg Subtype.val ((unitsHomeomorphNeZero (G₀ := ℂ)).apply_symm_apply (expNonzero z))
  let f (s : ℂ) : ℂˣ := b * expUnit (-L * s)
  have hexp : IsOpenQuotientMap expUnit := by
    apply (unitsHomeomorphNeZero (G₀ := ℂ)).symm.isOpenQuotientMap.comp (f := expNonzero)
    exact ⟨fun z ↦ ⟨Complex.log z, Subtype.ext (Complex.exp_log z.prop)⟩,
      Complex.isCoveringMap_exp.continuous, Complex.isCoveringMap_exp.isOpenMap⟩
  have hf : IsOpenQuotientMap f := (Homeomorph.mulLeft b).isOpenQuotientMap.comp
    (hexp.comp (Homeomorph.mulLeft₀ (-L) (neg_ne_zero.mpr hL)).isOpenQuotientMap)
  have hfiber (x y : ℂ) :
      f x = f y ↔ (QuotientAddGroup.mk x : ℂ ⧸ P) = QuotientAddGroup.mk y := by
    change b * expUnit (-L * x) = b * expUnit (-L * y) ↔ _
    rw [mul_left_cancel_iff, ← Units.val_inj, QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
    rw [hval, hval]
    change Complex.exp (-L * x) = Complex.exp (-L * y) ↔ ∃ k : ℤ, k • (T / L) = -x + y
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine exists_congr fun k ↦ ?_
    rw [zsmul_eq_mul, mul_div_assoc', div_eq_iff hL]
    change -L * x = -L * y + (k : ℂ) * T ↔ _
    constructor <;> intro h <;> linear_combination -h
  let g : (ℂ ⧸ P) → ℂˣ := Quotient.lift f (fun x y h ↦ (hfiber x y).mpr (Quotient.sound h))
  have hg : IsOpenQuotientMap g := (IsOpenQuotientMap.of_comp_iff
    (g := g) QuotientAddGroup.isOpenQuotientMap_mk).mp hf
  have hinj : Injective g := by
    intro x y
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact (hfiber u v).mp
  let e := (Equiv.ofBijective g ⟨hinj, hg.surjective⟩).toHomeomorphOfContinuousOpen
    hg.continuous hg.isOpenMap
  refine ⟨e, fun s ↦ ?_⟩
  change (b : ℂ) * (expUnit (-L * s) : ℂ) = _
  rw [hval]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hq).ne'),
    ← Complex.ofReal_log (zero_lt_one.trans hq).le, mul_neg, neg_mul]

end InfoGeometry.Analysis.MeromorphicPolarLiouvilleCylinder
