/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Dedekind zeta convergence and its prime-ideal Euler product

This owner proves the absolute convergence and Euler product for the Dedekind
zeta function of a number field in `re(s) > 1`, using Mathlib's definition of
`NumberField.dedekindZeta` and its ideal-norm API. It makes no claim about
analytic continuation or zeros.

The finite-sieve Euler-product argument is adapted from
`RiemannMasullo/ForMathlib/NumberTheory/EulerProduct/Basic.lean` and the
Dedekind-zeta specialization from
`RiemannMasullo/ForMathlib/NumberTheory/NumberField/DedekindZeta.lean` in
`mccorvie/riemann-masullo` (Apache-2.0, revision
`d5d6f7be10eac30c162e64eb6e856591927306c8`).
-/

noncomputable section

open Filter Ideal Set NumberField IsDedekindDomain
open scoped Topology

namespace InfoGeometry.Arithmetic.NumberFieldDedekindZetaEulerProduct

/-- Absolute convergence of the ideal Dirichlet series defining Dedekind zeta in `re(s) > 1`.

The coefficients count integral ideals by absolute norm; this is Mathlib's
`NumberField.dedekindZeta` Dirichlet series. -/
theorem dedekindZeta_LSeriesSummable (F : Type*) [Field F] [NumberField F] {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // I.absNorm = n} : ℂ)) s := by
  have hres := (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).eventually_ne
    (Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero F))
  obtain ⟨t, ht, ht'⟩ :=
    (hres.and (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs))).exists
  apply LSeriesSummable.of_re_le_re (s := (t : ℂ)) ht'.le
  by_contra hdiv
  exact ht (by
    rw [dedekindZeta, LSeries.eq_zero_of_not_LSeriesSummable _ _ hdiv, mul_zero])

set_option linter.style.haveILetI false in
/-- The sum of inverse powers of integral ideal norms converges above exponent one. -/
theorem summable_absNorm_rpow (F : Type*) [Field F] [NumberField F] {r : ℝ}
    (hr : 1 < r) :
    Summable fun I : Ideal (𝓞 F) ↦ (I.absNorm : ℝ) ^ (-r) := by
  classical
  let A (n : ℕ) : ℝ := Nat.card {I : Ideal (𝓞 F) // I.absNorm = n}
  have hsum : Summable (fun n : ℕ ↦ A n * (n : ℝ) ^ (-r)) := by
    apply (dedekindZeta_LSeriesSummable F (s := (r : ℂ)) hr).norm.congr
    intro n
    obtain rfl | hn := eq_or_ne n 0
    · simp [Real.zero_rpow (by linarith : -r ≠ 0)]
    · simp [hn, A, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  rw [← (Equiv.sigmaFiberEquiv (Ideal.absNorm (S := 𝓞 F))).summable_iff]
  have hfinite (n : ℕ) : Finite {I : Ideal (𝓞 F) // I.absNorm = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  refine (summable_sigma_of_nonneg (fun _ ↦ by dsimp; positivity)).2
    ⟨fun _ ↦ Summable.of_finite, hsum.congr fun n ↦ ?_⟩
  letI : Fintype {I : Ideal (𝓞 F) // I.absNorm = n} := Fintype.ofFinite _
  simp only [Equiv.sigmaFiberEquiv_apply, Function.comp_apply]
  rw [tsum_fintype]
  calc
    A n * (n : ℝ) ^ (-r) = ∑ _ : {I : Ideal (𝓞 F) // I.absNorm = n},
        (n : ℝ) ^ (-r) := by simp [A, Nat.card_eq_fintype_card]
    _ = ∑ I : {I : Ideal (𝓞 F) // I.absNorm = n},
        (I.val.absNorm : ℝ) ^ (-r) := by
      apply Finset.sum_congr rfl
      intro I _
      rw [I.property]

/-- A finite-sieve Euler product for a norm-summable multiplicative weight on a
commutative monoid with unique prime divisibility. -/
theorem hasProd_eulerFactors_of_summable {M ι : Type*} [CommMonoidWithZero M]
    [IsCancelMulZero M] (P : ι → M) (hp : ∀ i, Prime (P i))
    (hd : ∀ i j, P i ∣ P j → i = j)
    (hc : ∀ x : M, x ≠ 0 → x ≠ 1 → ∃ i, P i ∣ x) (f : M →*₀ ℂ)
    (hs : Summable fun x ↦ ‖f x‖) (h₁ : ∀ i, f (P i) ≠ 1) :
    HasProd (fun i ↦ (1 - f (P i))⁻¹) (∑' x, f x) := by
  classical
  let good (S : Finset ι) := {x : M | ∀ i ∈ S, ¬ P i ∣ x}
  let w (S : Finset ι) := (good S).indicator (f : M → ℂ)
  let R (S : Finset ι) := ∑' x, w S x
  have hsum (S) : Summable (w S) := (Summable.of_norm (f := fun x : M ↦ f x) hs).indicator _
  have hrec (S : Finset ι) (p : ι) (hpS : p ∉ S) :
      R (insert p S) = (1 - f (P p)) * R S := by
    let d := {x : M | P p ∣ x}.indicator (w S)
    have hdiff (x) : w (insert p S) x = w S x - d x := by
      by_cases h : P p ∣ x
      · have hbad : x ∉ good (insert p S) := fun hx ↦ hx p (Finset.mem_insert_self _ _) h
        simp [w, d, h, hbad]
      · have hiff : x ∈ good (insert p S) ↔ x ∈ good S := by simp [good, h]
        simp only [w, d, Set.indicator_apply, Set.mem_ofPred_eq, h, ite_false, sub_zero, hiff]
    have hcomp (x) : d (P p * x) = f (P p) * w S x := by
      have hiff : P p * x ∈ good S ↔ x ∈ good S := by
        constructor
        · exact fun hx i hi hix ↦ hx i hi (dvd_mul_of_dvd_right hix _)
        · intro hx i hi hdvd
          rcases (hp i).dvd_or_dvd hdvd with hip | hix
          · exact hpS (hd i p hip ▸ hi)
          · exact hx i hi hix
      simp only [d, w, Set.indicator_apply, Set.mem_ofPred_eq, dvd_mul_right, ite_true,
        hiff, map_mul, mul_ite, mul_zero]
    have hdv : Function.support d ⊆ Set.range (fun x ↦ P p * x) := by
      intro x hx
      by_contra hn
      have h : ¬ P p ∣ x := fun ⟨a, ha⟩ ↦ hn ⟨a, ha.symm⟩
      exact hx (by simp [d, h])
    have hinj : Function.Injective (fun x ↦ P p * x) :=
      fun _ _ ↦ mul_left_cancel₀ (hp p).ne_zero
    have hsumd : (∑' x, d x) = f (P p) * R S := by
      rw [← hinj.tsum_eq hdv, tsum_congr hcomp, tsum_mul_left]
    change (∑' x, w (insert p S) x) = _
    rw [tsum_congr hdiff, (hsum S).tsum_sub ((hsum S).indicator _), hsumd]
    change R S - f (P p) * R S = _
    ring
  have hfinite (S : Finset ι) :
      (∏ i ∈ S, (1 - f (P i))⁻¹) * R S = ∑' x, f x := by
    induction S using Finset.induction_on with
    | empty => simp [R, w, good]
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, hrec S i hi, ← ih]
      have hn : 1 - f (P i) ≠ 0 := sub_ne_zero.mpr (h₁ i).symm
      field_simp [hn]
  have hlim : Tendsto R atTop (𝓝 1) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := w)
      (g := fun x : M ↦ if x = 1 then (1 : ℂ) else 0) hs
    have hx (x : M) : Tendsto (fun S ↦ w S x) atTop (𝓝 (if x = 1 then (1 : ℂ) else 0)) := by
      apply tendsto_const_nhds.congr'
      by_cases h : x = 1
      · subst x
        exact .of_forall fun S ↦ by simp [w, good, fun i ↦ (hp i).not_dvd_one]
      by_cases h0 : x = 0
      · subst x
        exact .of_forall fun S ↦ by simp [w, Set.indicator_apply, h]
      obtain ⟨i, hi⟩ := hc x h0 h
      filter_upwards [Filter.eventually_finset_mem_atTop i] with S hiS
      have hbad : x ∉ good S := fun hs ↦ hs i hiS hi
      simp [w, hbad, h]
    have hb (S : Finset ι) (x : M) : ‖w S x‖ ≤ ‖f x‖ := by
      by_cases hx : x ∈ good S <;> simp [w, hx]
    simpa [R] using h hx (.of_forall hb)
  have hn := hlim.eventually_ne (one_ne_zero : (1 : ℂ) ≠ 0)
  have h := (tendsto_const_nhds (x := ∑' x, f x)).div hlim (by norm_num)
  rw [div_one] at h
  apply h.congr'
  filter_upwards [hn] with S hS
  exact (div_eq_iff hS).mpr (hfinite S).symm

/-- On its half-plane of absolute convergence, Dedekind zeta is the Euler product over
nonzero prime ideals of the ring of integers. -/
theorem dedekindZeta_hasProd (F : Type*) [Field F] [NumberField F] {s : ℂ}
    (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) ↦
      (1 - (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹) (dedekindZeta F s) := by
  classical
  have hs₀ : s ≠ 0 := fun h ↦ by simp [h] at hs; linarith
  let f : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun I := (I.absNorm : ℂ) ^ (-s)
      map_zero' := by simp [Complex.zero_cpow (neg_ne_zero.mpr hs₀)]
      map_one' := by simp
      map_mul' I J := by
        rw [map_mul, Nat.cast_mul]
        exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg I.absNorm)
          (Nat.cast_nonneg J.absNorm) _ }
  have hnorm (n : ℕ) : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
    obtain rfl | hn := eq_or_ne n 0
    · simp [Complex.zero_cpow (neg_ne_zero.mpr hs₀), Real.zero_rpow (by linarith : -s.re ≠ 0)]
    · exact Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn) _
  have hsum : Summable fun I ↦ ‖f I‖ :=
    (summable_absNorm_rpow F hs).congr fun I ↦ (hnorm I.absNorm).symm
  have hz : (∑' I, f I) = dedekindZeta F s := by
    let e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 F) → ℕ)
    have he : Summable (fun x ↦ f (e x)) := e.summable_iff.mpr hsum.of_norm
    rw [← e.tsum_eq, he.tsum_sigma]
    unfold dedekindZeta LSeries
    refine tsum_congr fun n ↦ ?_
    have hfinite : Finite {I : Ideal (𝓞 F) // I.absNorm = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    change (∑' I : {I : Ideal (𝓞 F) // I.absNorm = n},
      (I.val.absNorm : ℂ) ^ (-s)) = _
    rw [tsum_congr (fun I : {I : Ideal (𝓞 F) // I.absNorm = n} ↦
      congrArg (fun m : ℕ ↦ (m : ℂ) ^ (-s)) I.property), tsum_const,
      LSeries.term_of_ne_zero' hs₀, Complex.cpow_neg, nsmul_eq_mul, div_eq_mul_inv]
  rw [← hz]
  refine hasProd_eulerFactors_of_summable
    (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal) (fun v ↦ v.prime) ?_ ?_ f hsum ?_
  · intro v w hvw
    exact HeightOneSpectrum.ext
      (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp hvw)).symm
  · intro I hI htop
    obtain ⟨J, hJ, hIJ⟩ := I.exists_le_maximal (by simpa only [Ideal.one_eq_top] using htop)
    exact ⟨⟨J, hJ.isPrime, fun he ↦ hI (le_bot_iff.mp (he ▸ hIJ))⟩,
      Ideal.dvd_iff_le.mpr hIJ⟩
  · intro v he
    have hq : (1 : ℝ) < v.asIdeal.absNorm := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith : -s.re < 0)
    have hval := congrArg norm he
    change ‖(v.asIdeal.absNorm : ℂ) ^ (-s)‖ = ‖(1 : ℂ)‖ at hval
    rw [hnorm, norm_one] at hval
    exact hlt.ne hval

end InfoGeometry.Arithmetic.NumberFieldDedekindZetaEulerProduct

end noncomputable section
