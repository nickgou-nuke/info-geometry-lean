import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Arithmetic.RiemannZetaEquivalences

/-!
# Prime Euler-product convergence readback

This owner extracts the concrete analytic convergence already supplied by
Mathlib's Euler-product theorem.  It concerns the half-plane `Re s > 1` only;
it is not analytic continuation to the critical strip and makes no RH claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeEulerProductConvergenceBridge

open Filter Topology
open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences

/-- The finite prime cutoff of the bosonic Euler product. -/
def primeBosonicCutoff (n : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹

/-- A prime-indexed Euler factor, separated from its perturbation of `1`. -/
def primeEulerFactor (p : Nat.Primes) (s : ℂ) : ℂ :=
  (1 - (p : ℂ) ^ (-s))⁻¹

def primeEulerPerturbation (p : Nat.Primes) (s : ℂ) : ℂ :=
  primeEulerFactor p s - 1

/-! The natural-number cutoff, retyped as a finite set of prime subtypes. -/
def primeSubtypesBelow (n : ℕ) : Finset Nat.Primes :=
  (Nat.primesBelow n).attach.map
    ⟨fun p => ⟨p.1, (Nat.mem_primesBelow.mp p.2).2⟩,
      fun p q h => Subtype.ext (by simpa using Subtype.ext_iff.mp h)⟩

theorem prod_primeSubtypesBelow_eq (n : ℕ) (s : ℂ) :
    ∏ p ∈ primeSubtypesBelow n, primeEulerFactor p s =
      ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹ := by
  dsimp [primeSubtypesBelow, primeEulerFactor]
  rw [Finset.prod_map]
  exact Finset.prod_attach (Nat.primesBelow n) fun p => (1 - (p : ℂ) ^ (-s))⁻¹

/-! A concrete certificate interface for the missing local-uniform Euler
product estimate.  Once a summable majorant and continuity are supplied, the
Mathlib product M-test produces local uniform convergence. -/
theorem primeEulerProduct_locallyUniform_of_majorant
    {U : Set ℂ} (hU : IsOpen U) (u : Nat.Primes → ℝ)
    (hu : Summable u)
    (hbound : ∀ᶠ p : Nat.Primes in cofinite,
      ∀ s ∈ U, ‖primeEulerPerturbation p s‖ ≤ u p)
    (hcts : ∀ p : Nat.Primes, ContinuousOn (primeEulerPerturbation p) U) :
    HasProdLocallyUniformlyOn (fun p s => primeEulerFactor p s)
      (fun s => ∏' p : Nat.Primes, primeEulerFactor p s) U := by
  have h := Summable.hasProdLocallyUniformlyOn_one_add
    (K := U) hU hu hbound hcts
  simpa [primeEulerPerturbation, primeEulerFactor, add_sub_cancel]
    using h

/-! Each Euler factor is nonzero already at every finite cutoff in the
absolute-convergence half-plane.  Mathlib's prime-power norm bound makes the
argument independent of the limiting product. -/
theorem primeEulerFactor_ne_zero
    (p : ℕ) (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hpow : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hnorm := Complex.norm_prime_cpow_le_one_half ⟨p, hp⟩ hs
  rw [hpow, norm_one] at hnorm
  norm_num at hnorm

/-! The elementary local estimate behind the concrete Euler-product
majorant.  The prime-power norm bound gives `‖p⁻ˢ‖ ≤ 1/2`; the reverse
triangle inequality then keeps the denominator away from zero. -/
theorem primeEulerPerturbation_norm_le_two_norm_prime_cpow
    (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ‖primeEulerPerturbation p s‖ ≤
      2 * ‖(p : ℂ) ^ (-s)‖ := by
  let a : ℂ := (p : ℂ) ^ (-s)
  have ha : ‖a‖ ≤ (1 : ℝ) / 2 := by
    exact Complex.norm_prime_cpow_le_one_half p hs
  have hden : 1 - a ≠ 0 := by
    intro h
    apply primeEulerFactor_ne_zero p p.prop hs
    simpa [primeEulerFactor, a] using h
  have hden_pos : 0 < ‖1 - a‖ := norm_pos_iff.mpr hden
  have htri : (1 : ℝ) ≤ ‖1 - a‖ + ‖a‖ := by
    have h := norm_add_le (1 - a) a
    simpa [sub_add_cancel, norm_one] using h
  have hhalf : (1 : ℝ) / 2 ≤ ‖1 - a‖ := by
    linarith
  have hid : (1 - a)⁻¹ - 1 = a / (1 - a) := by
    have h_sub : 1 - (1 - a) = a := by ring
    have h_eq : (1 - a)⁻¹ - 1 = (1 - (1 - a)) / (1 - a) := by
      rw [sub_div, div_self hden, one_div]
    rw [h_eq, h_sub]
  change ‖(1 - a)⁻¹ - 1‖ ≤ 2 * ‖a‖
  rw [hid, norm_div]
  apply (div_le_iff₀ hden_pos).2
  calc
    ‖a‖ = 2 * ‖a‖ * ((1 : ℝ) / 2) := by ring
    _ ≤ 2 * ‖a‖ * ‖1 - a‖ := by
      gcongr

theorem primeEulerPerturbation_norm_le_two_prime_rpow
    (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ‖primeEulerPerturbation p s‖ ≤
      2 * (p : ℝ) ^ (-s.re) := by
  have hnorm := primeEulerPerturbation_norm_le_two_norm_prime_cpow p hs
  rw [Complex.norm_natCast_cpow_of_re_ne_zero p
    (by rw [neg_re]; linarith only [hs])] at hnorm
  simpa [neg_re] using hnorm

theorem primeEulerPerturbation_norm_le_on_re_ge
    (p : Nat.Primes) {s : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hs : 1 + δ ≤ s.re) :
    ‖primeEulerPerturbation p s‖ ≤
      2 * (p : ℝ) ^ (-(1 + δ)) := by
  have hbase : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast p.prop.one_le
  have hexp : -s.re ≤ -(1 + δ) := by linarith
  have hrpow : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(1 + δ)) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  calc
    ‖primeEulerPerturbation p s‖ ≤ 2 * (p : ℝ) ^ (-s.re) :=
      primeEulerPerturbation_norm_le_two_prime_rpow p (by linarith)
    _ ≤ 2 * (p : ℝ) ^ (-(1 + δ)) := by gcongr

theorem prime_rpow_majorant_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 + δ))) := by
  apply (Nat.Primes.summable_rpow).2
  linarith

theorem primeEulerProduct_locallyUniform_on_re_gt_one
    {U : Set ℂ} (hU : IsOpen U)
    (hRe : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ U, 1 + δ ≤ s.re)
    (hcts : ∀ p : Nat.Primes, ContinuousOn (primeEulerPerturbation p) U) :
    HasProdLocallyUniformlyOn (fun p s => primeEulerFactor p s)
      (fun s => ∏' p : Nat.Primes, primeEulerFactor p s) U := by
  rcases hRe with ⟨δ, hδ, hδU⟩
  let u : Nat.Primes → ℝ := fun p => 2 * (p : ℝ) ^ (-(1 + δ))
  have hu : Summable u := by
    simpa [u] using (prime_rpow_majorant_summable hδ).mul_left 2
  apply primeEulerProduct_locallyUniform_of_majorant hU u hu ?_ hcts
  exact Filter.Eventually.of_forall (fun p s hs => by
    simpa [u] using primeEulerPerturbation_norm_le_on_re_ge p hδ (hδU s hs))

theorem exists_positive_margin_of_compact_subset_re_gt_one
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ {s : ℂ | 1 < s.re}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ K, 1 + δ ≤ s.re := by
  by_cases hne : K.Nonempty
  · obtain ⟨s₀, hs₀, hmin⟩ := hK.exists_isMinOn hne continuous_re.continuousOn
    have hs₀_gt : 1 < s₀.re := hKsub hs₀
    refine ⟨(s₀.re - 1) / 2, by linarith, ?_⟩
    intro s hs
    have hle := hmin hs
    change s₀.re ≤ s.re at hle
    linarith
  · exact (Set.not_nonempty_iff_eq_empty.mp hne ▸ ⟨1, by norm_num, by simp⟩)

theorem primeEulerPerturbation_continuousOn_of_re_gt_one
    (p : Nat.Primes) {U : Set ℂ}
    (hU : U ⊆ {s : ℂ | 1 < s.re}) :
    ContinuousOn (primeEulerPerturbation p) U := by
  letI : NeZero (p : ℂ) := ⟨by exact_mod_cast p.prop.ne_zero⟩
  have hpow : ContinuousOn (fun s : ℂ => (p : ℂ) ^ (-s)) U := by
    exact (continuous_const_cpow (p : ℂ)).comp_continuousOn
      continuous_neg.continuousOn
  have hdencts : ContinuousOn (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) U :=
    continuous_const.continuousOn.sub hpow
  have hdenne : ∀ s ∈ U, 1 - (p : ℂ) ^ (-s) ≠ 0 := by
    intro s hs
    exact primeEulerFactor_ne_zero p p.prop (hU hs)
  have hinv := hdencts.inv₀ hdenne
  have hpert : ContinuousOn
      (fun s : ℂ => (1 - (p : ℂ) ^ (-s))⁻¹ - 1) U :=
    hinv.sub continuous_const.continuousOn
  simpa [primeEulerPerturbation, primeEulerFactor] using hpert

theorem primeEulerProduct_locallyUniform_on_re_margin
    {U : Set ℂ} (hU : IsOpen U)
    (hRe : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ U, 1 + δ ≤ s.re) :
    HasProdLocallyUniformlyOn (fun p s => primeEulerFactor p s)
      (fun s => ∏' p : Nat.Primes, primeEulerFactor p s) U := by
  apply primeEulerProduct_locallyUniform_on_re_gt_one hU hRe
  intro p
  rcases hRe with ⟨δ, hδ, hδU⟩
  apply primeEulerPerturbation_continuousOn_of_re_gt_one p
  intro s hs
  change 1 < s.re
  linarith [hδU s hs]

theorem compact_prime_majorant_bound
    {K : Set ℂ} (hK : IsCompact K)
    (hKsub : K ⊆ {s : ℂ | 1 < s.re}) :
    ∃ u : Nat.Primes → ℝ,
      Summable u ∧
        ∀ p : Nat.Primes, ∀ s ∈ K,
          ‖primeEulerPerturbation p s‖ ≤ u p := by
  rcases exists_positive_margin_of_compact_subset_re_gt_one hK hKsub with
    ⟨δ, hδ, hδK⟩
  let u : Nat.Primes → ℝ := fun p => 2 * (p : ℝ) ^ (-(1 + δ))
  refine ⟨u, ?_, ?_⟩
  · simpa [u] using (prime_rpow_majorant_summable hδ).mul_left 2
  · intro p s hs
    simpa [u] using primeEulerPerturbation_norm_le_on_re_ge p hδ (hδK s hs)

theorem primeEulerProduct_locallyUniform_on_halfPlane :
    HasProdLocallyUniformlyOn (fun p s => primeEulerFactor p s)
      (fun s => ∏' p : Nat.Primes, primeEulerFactor p s)
      {s : ℂ | 1 < s.re} := by
  apply hasProdLocallyUniformlyOn_of_forall_compact
    (isOpen_lt continuous_const continuous_re)
  intro K hKsub hK
  rcases exists_positive_margin_of_compact_subset_re_gt_one hK hKsub with
    ⟨δ, hδ, hδK⟩
  let U : Set ℂ := {s : ℂ | 1 + δ / 2 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUmargin : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ U, 1 + ε ≤ s.re := by
    refine ⟨δ / 2, by linarith, ?_⟩
    intro s hs
    exact le_of_lt hs
  have hUprod := primeEulerProduct_locallyUniform_on_re_margin hU hUmargin
  have hKU : K ⊆ U := by
    intro s hs
    change 1 + δ / 2 < s.re
    have hle := hδK s hs
    linarith
  exact (hUprod.mono hKU).hasProdUniformlyOn_of_isCompact hK

theorem primeEulerProduct_tprod_eq_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    (∏' p : Nat.Primes, primeEulerFactor p s) = riemannZeta s := by
  simpa [primeEulerFactor] using riemannZeta_eulerProduct_tprod hs

theorem primeEulerProduct_locallyUniform_to_riemannZeta :
    HasProdLocallyUniformlyOn (fun p s => primeEulerFactor p s)
      (fun s => riemannZeta s) {s : ℂ | 1 < s.re} := by
  have hprod := primeEulerProduct_locallyUniform_on_halfPlane
  rw [HasProdLocallyUniformlyOn] at hprod ⊢
  apply hprod.congr_right
  intro s hs
  exact primeEulerProduct_tprod_eq_riemannZeta hs

theorem primeBosonicCutoff_ne_zero
    {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    primeBosonicCutoff n s ≠ 0 := by
  dsimp [primeBosonicCutoff]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hp_prime : p.Prime := (Nat.mem_primesBelow.mp hp).2
  exact inv_ne_zero (primeEulerFactor_ne_zero p hp_prime hs)

/-! The finite cutoff converges to the concrete Riemann zeta function in the
Euler-product half-plane. -/
theorem primeBosonicCutoff_tendsto_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun n : ℕ => primeBosonicCutoff n s) atTop
      (𝓝 (riemannZeta s)) := by
  simpa [primeBosonicCutoff] using
    (riemannZeta_eulerProduct hs)

/-! The limit is nonzero in the same half-plane. -/
theorem primeBosonicCutoff_limit_ne_zero
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

/-! Consequently the finite cutoffs are eventually nonzero. -/
theorem eventually_primeBosonicCutoff_ne_zero
    {s : ℂ} (hs : 1 < s.re) :
    ∀ᶠ n : ℕ in atTop, primeBosonicCutoff n s ≠ 0 := by
  have hconv := primeBosonicCutoff_tendsto_riemannZeta hs
  exact hconv.eventually
    (isOpen_ne.mem_nhds (riemannZeta_ne_zero_of_one_lt_re hs))

/-! ## Completed finite cutoffs in the absolute-convergence half-plane -/

/-- Add the pole-cancelling and Archimedean factors to a finite Euler cutoff. -/
def primeCompletedCutoff (n : ℕ) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s * primeBosonicCutoff n s

/-- The completed finite cutoff converges to the concrete `riemannXi` readout
on `Re(s) > 1`.  This is a genuine prime-to-`ξ` convergence theorem, but only
on the absolute-convergence half-plane; no continuation into the critical strip
is inferred here. -/
theorem primeCompletedCutoff_tendsto_riemannXi
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun n : ℕ => primeCompletedCutoff n s) atTop
      (𝓝 (riemannXi s)) := by
  have hcut := primeBosonicCutoff_tendsto_riemannZeta hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hGamma : Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hcompleted : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    have h := riemannZeta_def_of_ne_zero hs0
    rw [mul_comm]
    exact (eq_div_iff hGamma).mp h |>.symm
  have hprod :
      Tendsto
        (fun n : ℕ =>
          ((1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s) * primeBosonicCutoff n s)
        atTop
        (𝓝 (((1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s) * riemannZeta s)) := by
    exact tendsto_const_nhds.mul hcut
  simpa [primeCompletedCutoff, riemannXi, hcompleted, mul_assoc] using hprod

/-- The same cutoff converges to the pole-removed entire representative on
`Re(s) > 1`, where the meromorphic and entire readouts coincide. -/
theorem primeCompletedCutoff_tendsto_entireRiemannXi
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun n : ℕ => primeCompletedCutoff n s) atTop
      (𝓝 (InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge.entireRiemannXi s)) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have heq : riemannXi s =
      InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge.entireRiemannXi s :=
    (InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge.entireRiemannXi_eq_riemannXi
      hs0 hs1).symm
  simpa [heq] using primeCompletedCutoff_tendsto_riemannXi hs

/-- The completed prime cutoffs are eventually nonzero in `Re(s) > 1`. -/
theorem eventually_primeCompletedCutoff_ne_zero
    {s : ℂ} (hs : 1 < s.re) :
    ∀ᶠ n : ℕ in atTop, primeCompletedCutoff n s ≠ 0 := by
  have hconv := primeCompletedCutoff_tendsto_riemannXi hs
  exact hconv.eventually
    (isOpen_ne.mem_nhds (riemannXi_ne_zero_of_one_lt_re hs))

/-! ## Generic compact-tail criterion for the missing local-uniform arrow -/

/-! If a sequence of complex functions has uniform Cauchy tails on every
compact set and converges pointwise, then its convergence is locally uniform.
This is a direct wrapper around Mathlib's uniform-Cauchy convergence theorem;
it is the reusable analytic criterion needed by a concrete prime model. -/
theorem locallyUniformly_of_compact_uniformCauchy
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (h_tail : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ N₀, ∀ m n : ℕ, N₀ ≤ m → N₀ ≤ n →
        ∀ z ∈ K, dist (F m z) (F n z) < ε)
    (h_point : ∀ z : ℂ, Tendsto (fun n : ℕ => F n z) atTop (𝓝 (f z))) :
    TendstoLocallyUniformly F f atTop := by
  apply (tendstoLocallyUniformly_iff_forall_isCompact).2
  intro K hK
  apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
  · intro u hu
    rcases Metric.mem_uniformity_dist.mp hu with ⟨ε, hε, hεu⟩
    rcases h_tail K hK ε hε with ⟨N₀, hN₀⟩
    have hge : ∀ᶠ n : ℕ in atTop, N₀ ≤ n := eventually_ge_atTop N₀
    filter_upwards [hge.prod_mk hge] with mn hmn z hz
    exact hεu (hN₀ mn.1 mn.2 hmn.1 hmn.2 z hz)
  · intro z hz
    exact h_point z

end InfoGeometry.Canonical.PrimeEulerProductConvergenceBridge
