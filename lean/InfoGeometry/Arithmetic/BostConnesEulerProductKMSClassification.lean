/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.BostConnesNativeZetaPartition
import InfoGeometry.Arithmetic.BostConnesActualZetaResidueNormalization
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

/-!
# Bost–Connes Infinite Euler Product, Hecke `*`-Algebra KMS Equations & State Recurrence

Advances Frontier 2 ("Full infinite-Euler-product `C*`-algebraic Bost–Connes KMS classification")
by establishing three kernel-checked pillars anchored directly in Mathlib's infinite Euler product
for `riemannZeta` and `InfoGeometry.Arithmetic.BostConnesNativeZetaPartition`:

1. **Infinite Euler Product of the Bost–Connes Partition Function (`β > 1`)**:
   - `bc_partitionSeries_eulerProduct_hasProd`, `bc_partitionSeries_eulerProduct_tprod`,
     `bc_partitionSeries_eulerProduct_tendsto`: proves `partitionSeries (β : ℂ) = ∏' p : Nat.Primes, (1 - p^(-β))⁻¹`
     for all `1 < β` and convergence of finite prime cutoffs, plus `bc_partitionSeries_ne_zero`.
2. **Bost–Connes Hecke Algebra (`BostConnesHeckeSystem`) & `KMS_β` Forced Constraints**:
   - Defines `BostConnesHeckeSystem` with isometries `μ_n`, `μ_n^*`, `e(r)` (`r ∈ ℚ`), and the
     defining **Hecke averaging relation** `μ_n e(r) μ_n^* = n⁻¹ ∑_{k=0}^{n-1} e((r + k)/n)`.
   - Defines `IsBCKMSState` on linear functionals `φ : A →ₗ[ℂ] ℂ` and proves:
     * `kms_range_proj_eval`: `φ(μ_n μ_n^*) = n^{-β}`
     * `kms_hecke_character_recurrence`: `n⁻¹ ∑_{k=0}^{n-1} φ(e((r+k)/n)) = n^{-β} φ(e(r))`
     * `kms_prime_primitive_avg`: for every prime `p`, `∑_{k=1}^{p-1} φ(e(k/p)) = p^{1-β} - 1`
     * `kms_prime_symmetric_unique`: any `Gal(ℚ^{ab}/ℚ)`-invariant `KMS_β` state is uniquely forced
       on primitive `p`-th roots of unity to `(p^{1-β} - 1) / (p - 1)`
     * `kms_prime_critical_vanishing`: at `β = 1`, primitive `p`-th root averages vanish identically.
3. **Exact Infinite-Euler-Product Hecke-KMS Functional Verification (`β > 1`)**:
   - Defines `bcEulerCharacterState β σ r` normalized by `(partitionSeries β)⁻¹` for bounded
     completely multiplicative character phases `σ : ℕ → ℂ`.
   - Proves absolute summability (`bcEulerCharacterState_summable`), normalization `bcEulerCharacterState_zero = 1`,
     periodicity (`bcEulerCharacterState_periodic`), and the exact Hecke averaging recurrence
     `bcEulerCharacterState_hecke_recurrence` (and `bcEulerCharacterState_one_hecke_recurrence`
     for `σ = 1`) over all `m : ℕ+`, `r : ℚ`.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE & ANALYTIC THEOREMS
* `bc_partitionSeries_eulerProduct_hasProd`, `bc_partitionSeries_eulerProduct_tprod`,
  `bc_partitionSeries_eulerProduct_tendsto`, `bc_partitionSeries_ne_zero`.
* `kms_range_proj_eval`, `kms_hecke_character_recurrence`, `kms_prime_primitive_avg`,
  `kms_prime_symmetric_unique`, `kms_prime_critical_vanishing`.
* `bcEulerCharacterState_summable`, `bcEulerCharacterState_zero`,
  `bcEulerCharacterState_periodic`, `bcEulerCharacterState_hecke_recurrence`,
  `bcEulerCharacterState_one_hecke_recurrence`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* Symmetrized primitive-root evaluation `kms_prime_symmetric_unique` conditional on `Gal`-invariance
  across primitive `p`-th roots; Hecke recurrence on `bcEulerCharacterState` conditional on `1 < β`
  and complete multiplicativity of `σ`.

#### BUCKET 3: OPEN CLOSURE DEBT
* Universal `C*`-enveloping norm completion of the Bost–Connes Hecke algebra, uniqueness of the
  `KMS_β` state for `0 < β ≤ 1` in the `C*`-algebraic sense, and full Choquet extreme-point
  parametrization by `\widehat{\mathbb{Z}}^\times` on the completed `C*`-algebra remain open
  beyond Mathlib's present `C*`-algebraic KMS library.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.BostConnesEulerProductKMSClassification

open scoped BigOperators
open Filter Topology
open InfoGeometry.Arithmetic.BostConnesNativeZetaPartition

/-! ## 1. Infinite Euler Product of the Bost–Connes Partition Function (`β > 1`) -/

theorem bc_partitionSeries_eulerProduct_hasProd {β : ℝ} (hβ : 1 < β) :
    HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-(β : ℂ)))⁻¹) (partitionSeries (β : ℂ)) := by
  have hs : 1 < (β : ℂ).re := by simpa using hβ
  rw [partitionSeries_eq_riemannZeta hs]
  exact riemannZeta_eulerProduct_hasProd hs

theorem bc_partitionSeries_eulerProduct_tprod {β : ℝ} (hβ : 1 < β) :
    (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-(β : ℂ)))⁻¹) = partitionSeries (β : ℂ) :=
  (bc_partitionSeries_eulerProduct_hasProd hβ).tprod_eq

theorem bc_partitionSeries_eulerProduct_tendsto {β : ℝ} (hβ : 1 < β) :
    Tendsto
      (fun n : ℕ => ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-(β : ℂ)))⁻¹)
      atTop (𝓝 (partitionSeries (β : ℂ))) := by
  have hs : 1 < (β : ℂ).re := by simpa using hβ
  rw [partitionSeries_eq_riemannZeta hs]
  exact riemannZeta_eulerProduct hs

theorem bc_partitionSeries_ne_zero {β : ℝ} (hβ : 1 < β) :
    partitionSeries (β : ℂ) ≠ 0 :=
  partitionSeries_ne_zero (by simpa using hβ)

/-! ## 2. Bost–Connes Hecke `*`-Algebra & `KMS_β` Functional Equations -/

/-- The Bost–Connes Hecke algebra over `ℂ` generated by partial isometries `μ n` (`n : ℕ+`) and
cyclotomic group elements `e r` (`r : ℚ`) satisfying the defining Hecke averaging relation. -/
structure BostConnesHeckeSystem (A : Type*) [Ring A] [Algebra ℂ A] where
  μ : ℕ+ → A
  μ_star : ℕ+ → A
  e : ℚ → A
  μ_star_mul_μ : ∀ n : ℕ+, μ_star n * μ n = 1
  μ_mul : ∀ m n : ℕ+, μ (m * n) = μ m * μ n
  μ_star_mul : ∀ m n : ℕ+, μ_star (m * n) = μ_star n * μ_star m
  e_zero : e 0 = 1
  e_add : ∀ r s : ℚ, e (r + s) = e r * e s
  e_periodic : ∀ r : ℚ, e (r + 1) = e r
  hecke_avg :
    ∀ (n : ℕ+) (r : ℚ),
      μ n * e r * μ_star n = ((n : ℂ)⁻¹) • ∑ k : Fin n, e ((r + k.1) / n)

/-- KMS condition on a normalized `ℂ`-linear functional `φ : A →ₗ[ℂ] ℂ` for `BostConnesHeckeSystem A`
at inverse temperature `β`. -/
structure IsBCKMSState {A : Type*} [Ring A] [Algebra ℂ A]
    (sys : BostConnesHeckeSystem A) (β : ℝ) (φ : A →ₗ[ℂ] ℂ) : Prop where
  map_one : φ 1 = 1
  kms_scale : ∀ (n : ℕ+) (a : A), φ (sys.μ n * a * sys.μ_star n) = ((n : ℂ) ^ (-(β : ℂ))) * φ a
  kms_offdiag : ∀ (r : ℚ) (m n : ℕ+), m ≠ n → φ (sys.e r * sys.μ m * sys.μ_star n) = 0

theorem kms_range_proj_eval {A : Type*} [Ring A] [Algebra ℂ A]
    {sys : BostConnesHeckeSystem A} {β : ℝ} {φ : A →ₗ[ℂ] ℂ}
    (hφ : IsBCKMSState sys β φ) (n : ℕ+) :
    φ (sys.μ n * sys.μ_star n) = (n : ℂ) ^ (-(β : ℂ)) := by
  have h1 : sys.μ n * 1 * sys.μ_star n = sys.μ n * sys.μ_star n := by simp
  rw [← h1, hφ.kms_scale n 1, hφ.map_one, mul_one]

/-- Exact Hecke character recurrence forced by any `KMS_β` state on `e(r)`. -/
theorem kms_hecke_character_recurrence {A : Type*} [Ring A] [Algebra ℂ A]
    {sys : BostConnesHeckeSystem A} {β : ℝ} {φ : A →ₗ[ℂ] ℂ}
    (hφ : IsBCKMSState sys β φ) (n : ℕ+) (r : ℚ) :
    ((n : ℂ)⁻¹) * ∑ k : Fin n, φ (sys.e ((r + k.1) / n)) =
      ((n : ℂ) ^ (-(β : ℂ))) * φ (sys.e r) := by
  have hL := congrArg φ (sys.hecke_avg n r)
  rw [hφ.kms_scale n (sys.e r)] at hL
  rw [map_smul, smul_eq_mul, map_sum] at hL
  exact hL.symm

/-- Exact primitive `p`-th root sum identity forced by `KMS_β` at every prime `p`. -/
theorem kms_prime_primitive_avg {A : Type*} [Ring A] [Algebra ℂ A]
    {sys : BostConnesHeckeSystem A} {β : ℝ} {φ : A →ₗ[ℂ] ℂ}
    (hφ : IsBCKMSState sys β φ) (p : ℕ) (hp : Nat.Prime p) :
    ∑ k ∈ Finset.Ico 1 p, φ (sys.e ((k : ℚ) / p)) = (p : ℂ) ^ (1 - (β : ℂ)) - 1 := by
  let pPos : ℕ+ := ⟨p, hp.pos⟩
  have hrec := kms_hecke_character_recurrence hφ pPos 0
  have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have he0 : φ (sys.e 0) = 1 := by rw [sys.e_zero, hφ.map_one]
  have hmul := congrArg (fun z : ℂ => (p : ℂ) * z) hrec
  have hlhs :
      (p : ℂ) * (((pPos : ℂ)⁻¹) * ∑ k : Fin pPos, φ (sys.e ((0 + k.1) / pPos))) =
        ∑ k ∈ Finset.range p, φ (sys.e ((k : ℚ) / p)) := by
    have hpcoe : (pPos : ℂ) = (p : ℂ) := rfl
    rw [hpcoe, ← mul_assoc, mul_inv_cancel₀ hp_ne, one_mul]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => φ (sys.e ((0 + (k : ℚ)) / pPos)))]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [pPos]
  have hsplit :
      ∑ k ∈ Finset.range p, φ (sys.e ((k : ℚ) / p)) =
        1 + ∑ k ∈ Finset.Ico 1 p, φ (sys.e ((k : ℚ) / p)) := by
    have hsplit_gen :
        ∑ k ∈ Finset.range p, φ (sys.e ((k : ℚ) / p)) =
          φ (sys.e ((0 : ℚ) / p)) + ∑ k ∈ Finset.Ico 1 p, φ (sys.e ((k : ℚ) / p)) := by
      have h0 : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
      have hs := Finset.add_sum_erase (Finset.range p) (fun k => φ (sys.e ((k : ℚ) / p))) h0
      have herase : (Finset.range p).erase 0 = Finset.Ico 1 p := by
        ext k
        simp [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [herase] at hs
      exact hs.symm
    have hzero_arg : ((0 : ℚ) / p) = 0 := zero_div _
    rw [hzero_arg, he0] at hsplit_gen
    exact hsplit_gen
  have hrhs : (p : ℂ) * (((pPos : ℂ) ^ (-(β : ℂ))) * φ (sys.e 0)) = (p : ℂ) ^ (1 - (β : ℂ)) := by
    have hcp : (p : ℂ) ^ (1 : ℂ) * (p : ℂ) ^ (-(β : ℂ)) = (p : ℂ) ^ (1 - (β : ℂ)) := by
      rw [← Complex.cpow_add 1 (-(β : ℂ)) hp_ne, sub_eq_add_neg]
    rw [Complex.cpow_one] at hcp
    have hpcoe : (pPos : ℂ) = (p : ℂ) := rfl
    rw [hpcoe, he0, mul_one, hcp]
  rw [hlhs, hsplit, hrhs] at hmul
  exact eq_sub_of_add_eq' hmul

/-- Any Galois-invariant `KMS_β` state on `p`-th roots of unity is uniquely pinned to
`(p^{1-β} - 1) / (p - 1)`. -/
theorem kms_prime_symmetric_unique {A : Type*} [Ring A] [Algebra ℂ A]
    {sys : BostConnesHeckeSystem A} {β : ℝ} {φ : A →ₗ[ℂ] ℂ}
    (hφ : IsBCKMSState sys β φ) (p : ℕ) (hp : Nat.Prime p) (c : ℂ)
    (hgal : ∀ k ∈ Finset.Ico 1 p, φ (sys.e ((k : ℚ) / p)) = c) :
    c = ((p : ℂ) ^ (1 - (β : ℂ)) - 1) / ((p : ℂ) - 1) := by
  have hsum := kms_prime_primitive_avg hφ p hp
  have hcongr : ∑ k ∈ Finset.Ico 1 p, φ (sys.e ((k : ℚ) / p)) = (p - 1 : ℕ) * c := by
    rw [Finset.sum_congr rfl hgal, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  rw [hcongr] at hsum
  have hp1 : 1 ≤ p := hp.one_le
  have hpm1_ne : ((p : ℂ) - 1) ≠ 0 := by
    intro h0
    have hpeq : (p : ℂ) = 1 := sub_eq_zero.mp h0
    have hp_nat : p = 1 := by exact_mod_cast hpeq
    exact hp.ne_one hp_nat
  have hcast : ((p - 1 : ℕ) : ℂ) = (p : ℂ) - 1 := by
    rw [Nat.cast_sub hp1, Nat.cast_one]
  rw [hcast] at hsum
  exact eq_div_of_mul_eq hpm1_ne (by rw [mul_comm, hsum])

/-- At critical inverse temperature `β = 1`, the primitive `p`-th root character sum vanishes. -/
theorem kms_prime_critical_vanishing {A : Type*} [Ring A] [Algebra ℂ A]
    {sys : BostConnesHeckeSystem A} {φ : A →ₗ[ℂ] ℂ}
    (hφ : IsBCKMSState sys 1 φ) (p : ℕ) (hp : Nat.Prime p) :
    ∑ k ∈ Finset.Ico 1 p, φ (sys.e ((k : ℚ) / p)) = 0 := by
  rw [kms_prime_primitive_avg hφ p hp]
  simp

/-! ## 3. Exact Infinite-Euler-Product Hecke-KMS Functional Verification (`β > 1`) -/

/-- Infinite-series Bost–Connes `β > 1` state on `ℚ/ℤ` driven by a bounded multiplicative phase
`σ : ℕ → ℂ` and normalized by `(partitionSeries β)⁻¹`. -/
def bcEulerCharacterState (β : ℝ) (σ : ℕ → ℂ) (r : ℚ) : ℂ :=
  (partitionSeries (β : ℂ))⁻¹ *
    ∑' n : ℕ,
      if n = 0 then 0
      else ((n : ℂ) ^ (-(β : ℂ))) * σ n * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (n : ℂ))

private lemma norm_exp_two_pi_I_mul_real (x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))‖ = 1 := by
  have harg : 2 * Real.pi * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

theorem bcEulerCharacterState_summable {β : ℝ} (hβ : 1 < β) (σ : ℕ → ℂ)
    (hσ : ∀ n : ℕ, ‖σ n‖ ≤ 1) (r : ℚ) :
    Summable (fun n : ℕ =>
      if n = 0 then (0 : ℂ)
      else ((n : ℂ) ^ (-(β : ℂ))) * σ n * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (n : ℂ))) := by
  have hreal : Summable (fun n : ℕ => ((n : ℝ) ^ (-β))) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _), one_div] using
      (Real.summable_nat_rpow_inv.mpr hβ)
  refine Summable.of_norm_bounded hreal fun n => ?_
  by_cases hn : n = 0
  · subst hn
    have h0 : (-β) ≠ 0 := by linarith
    simp [Real.zero_rpow h0]
  · simp only [hn, ↓reduceIte, norm_mul]
    have hpos : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hcpow : ‖(n : ℂ) ^ (-(β : ℂ))‖ = (n : ℝ) ^ (-β) := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (n : ℂ))‖ = 1 := by
      have harg :
          2 * Real.pi * Complex.I * (r : ℂ) * (n : ℂ) =
            2 * Real.pi * Complex.I * (((r : ℝ) * (n : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg]
      exact norm_exp_two_pi_I_mul_real ((r : ℝ) * (n : ℝ))
    rw [hcpow, hexp, mul_one]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hpos _) (hσ n)

theorem bcEulerCharacterState_zero {β : ℝ} (hβ : 1 < β) (σ : ℕ → ℂ)
    (hσ_one : ∀ n : ℕ, n ≠ 0 → σ n = 1) :
    bcEulerCharacterState β σ 0 = 1 := by
  unfold bcEulerCharacterState
  have hsum_base : Summable (fun n : ℕ =>
      if n = 0 then (0 : ℂ)
      else ((n : ℂ) ^ (-(β : ℂ))) * (if n = 0 then 0 else (1 : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * ((0 : ℚ) : ℂ) * (n : ℂ))) :=
    bcEulerCharacterState_summable hβ (fun n => if n = 0 then 0 else 1)
      (fun n => by split_ifs <;> simp) 0
  have hfun : (fun n : ℕ =>
      if n = 0 then (0 : ℂ)
      else ((n : ℂ) ^ (-(β : ℂ))) * σ n *
        Complex.exp (2 * Real.pi * Complex.I * ((0 : ℚ) : ℂ) * (n : ℂ))) =
      fun n : ℕ =>
        if n = 0 then (0 : ℂ)
        else ((n : ℂ) ^ (-(β : ℂ))) * (if n = 0 then 0 else (1 : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * ((0 : ℚ) : ℂ) * (n : ℂ)) := by
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, hσ_one n hn]
  have hsum0 : Summable (fun n : ℕ =>
      if n = 0 then (0 : ℂ)
      else ((n : ℂ) ^ (-(β : ℂ))) * σ n *
        Complex.exp (2 * Real.pi * Complex.I * ((0 : ℚ) : ℂ) * (n : ℂ))) := by
    rw [hfun]
    exact hsum_base
  have hpart :
      (∑' n : ℕ,
        if n = 0 then (0 : ℂ)
        else ((n : ℂ) ^ (-(β : ℂ))) * σ n *
          Complex.exp (2 * Real.pi * Complex.I * ((0 : ℚ) : ℂ) * (n : ℂ))) =
        partitionSeries (β : ℂ) := by
    rw [hsum0.tsum_eq_zero_add]
    simp only [↓reduceIte, zero_add]
    unfold partitionSeries
    refine tsum_congr fun n => ?_
    simp [hσ_one (n + 1) (Nat.succ_ne_zero n), one_div, Complex.cpow_neg]
  rw [hpart, inv_mul_cancel₀ (bc_partitionSeries_ne_zero hβ)]

theorem bcEulerCharacterState_periodic (β : ℝ) (σ : ℕ → ℂ) (r : ℚ) :
    bcEulerCharacterState β σ (r + 1) = bcEulerCharacterState β σ r := by
  unfold bcEulerCharacterState
  congr 1
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    congr 1
    have harg :
        2 * Real.pi * Complex.I * (((r + 1 : ℚ) : ℂ)) * (n : ℂ) =
          2 * Real.pi * Complex.I * (r : ℂ) * (n : ℂ) + (n : ℤ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma finite_root_of_unity_sum (m : ℕ+) (n : ℕ) :
    ∑ k : Fin m, Complex.exp (2 * Real.pi * Complex.I * (k.1 : ℂ) * (n : ℂ) / (m : ℂ)) =
      if (m : ℕ) ∣ n then (m : ℂ) else 0 := by
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (m : ℂ))
  have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hterm :
      (∑ k : Fin m, Complex.exp (2 * Real.pi * Complex.I * (k.1 : ℂ) * (n : ℂ) / (m : ℂ))) =
        ∑ k ∈ Finset.range m, z ^ k := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (n : ℂ) / (m : ℂ)))]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [hterm]
  by_cases hdvd : (m : ℕ) ∣ n
  · rw [if_pos hdvd]
    rcases hdvd with ⟨d, rfl⟩
    have hz1 : z = 1 := by
      dsimp [z]
      have harg :
          2 * Real.pi * Complex.I * (((m * d : ℕ) : ℂ)) / (m : ℂ) =
            (d : ℤ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp [hm_ne]
      rw [harg]
      exact Complex.exp_int_mul_two_pi_mul_I d
    simp [hz1]
  · rw [if_neg hdvd]
    have hzm : z ^ (m : ℕ) = 1 := by
      dsimp [z]
      rw [← Complex.exp_nat_mul]
      have harg :
          ((m : ℕ) : ℂ) * (2 * Real.pi * Complex.I * (n : ℂ) / (m : ℂ)) =
            (n : ℤ) * (2 * Real.pi * Complex.I) := by
        field_simp [hm_ne]
        push_cast
        ring
      rw [harg]
      exact Complex.exp_int_mul_two_pi_mul_I n
    have hz_ne1 : z ≠ 1 := by
      intro hz1
      dsimp [z] at hz1
      rw [Complex.exp_eq_one_iff] at hz1
      rcases hz1 with ⟨q, hq⟩
      have h2pi_ne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hq' : (n : ℂ) / (m : ℂ) = (q : ℂ) := by
        apply mul_left_cancel₀ h2pi_ne
        calc
          (2 * Real.pi * Complex.I) * ((n : ℂ) / (m : ℂ))
              = 2 * Real.pi * Complex.I * (n : ℂ) / (m : ℂ) := by ring
          _ = (q : ℂ) * (2 * Real.pi * Complex.I) := hq
          _ = (2 * Real.pi * Complex.I) * (q : ℂ) := by ring
      have hmul_c : (n : ℂ) = (q : ℂ) * (m : ℂ) := (div_eq_iff hm_ne).mp hq'
      have hmul_z : (n : ℤ) = q * (m : ℤ) := by exact_mod_cast hmul_c
      have hdvd_z : (m : ℤ) ∣ (n : ℤ) := ⟨q, by linarith⟩
      exact hdvd (Int.natCast_dvd_natCast.mp hdvd_z)
    have hgeom := geom_sum_mul z m
    rw [hzm, sub_self] at hgeom
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero (sub_ne_zero.mpr hz_ne1) hgeom

private lemma tsum_ite_dvd_eq_tsum_mul (m : ℕ+) (f : ℕ → ℂ) :
    (∑' n : ℕ, if (m : ℕ) ∣ n then f n else 0) = ∑' d : ℕ, f ((m : ℕ) * d) := by
  let g : ℕ → ℕ := fun d => (m : ℕ) * d
  have hg : Function.Injective g := mul_right_injective₀ m.ne_zero
  have hsupp : Function.support (fun n : ℕ => if (m : ℕ) ∣ n then f n else 0) ⊆ Set.range g := by
    intro n hn
    rw [Function.mem_support] at hn
    by_cases hdvd : (m : ℕ) ∣ n
    · rcases hdvd with ⟨d, rfl⟩
      exact ⟨d, rfl⟩
    · exact absurd (if_neg hdvd) hn
  rw [← hg.tsum_eq hsupp]
  refine tsum_congr fun d => ?_
  have hdvd : (m : ℕ) ∣ ((m : ℕ) * d) := ⟨d, rfl⟩
  exact if_pos hdvd

private def bcEulerTerm (β : ℝ) (σ : ℕ → ℂ) (q : ℚ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else ((n : ℂ) ^ (-(β : ℂ))) * σ n * Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (n : ℂ))

private lemma bcEulerCharacterState_eq_mul_tsum_term (β : ℝ) (σ : ℕ → ℂ) (q : ℚ) :
    bcEulerCharacterState β σ q = (partitionSeries (β : ℂ))⁻¹ * ∑' n : ℕ, bcEulerTerm β σ q n :=
  rfl

private lemma complex_hecke_cancel (m_c Z C S : ℂ) (hm : m_c ≠ 0) :
    m_c⁻¹ * (Z * (m_c * (C * S))) = C * (Z * S) := by
  field_simp [hm]

/-- **Exact Infinite-Euler-Product Hecke-KMS Functional Identity (`β > 1`)**:
for any bounded completely multiplicative character `σ`, the normalized Euler-product state
satisfies `m⁻¹ ∑_{k=0}^{m-1} φ_{β,σ}((r + k)/m) = m^{-β} σ(m) φ_{β,σ}(r)`. -/
theorem bcEulerCharacterState_hecke_recurrence
    {β : ℝ} (hβ : 1 < β) (σ : ℕ → ℂ)
    (hσ_mul : ∀ a b : ℕ, σ (a * b) = σ a * σ b)
    (hσ_bd : ∀ n : ℕ, ‖σ n‖ ≤ 1)
    (m : ℕ+) (r : ℚ) :
    ((m : ℂ)⁻¹) * ∑ k : Fin m, bcEulerCharacterState β σ ((r + k.1) / m) =
      ((m : ℂ) ^ (-(β : ℂ))) * σ m * bcEulerCharacterState β σ r := by
  have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hsum_q : ∀ q : ℚ, Summable (bcEulerTerm β σ q) := fun q =>
    bcEulerCharacterState_summable hβ σ hσ_bd q
  have hswap :
      ∑ k : Fin m, (∑' n : ℕ, bcEulerTerm β σ ((r + k.1) / m) n) =
        ∑' n : ℕ, ∑ k : Fin m, bcEulerTerm β σ ((r + k.1) / m) n :=
    (Summable.tsum_finsetSum (s := (Finset.univ : Finset (Fin m)))
      (f := fun k : Fin m => bcEulerTerm β σ ((r + k.1) / m))
      (fun k _ => hsum_q ((r + k.1) / m))).symm
  have hinner_pt :
      ∀ n : ℕ, (∑ k : Fin m, bcEulerTerm β σ ((r + k.1) / m) n) =
        if (m : ℕ) ∣ n then (m : ℂ) * bcEulerTerm β σ (r / m) n else 0 := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [bcEulerTerm]
    · have hexp_split :
          ∀ k : Fin m,
            bcEulerTerm β σ ((r + k.1) / m) n =
              bcEulerTerm β σ (r / m) n *
                Complex.exp (2 * Real.pi * Complex.I * (k.1 : ℂ) * (n : ℂ) / (m : ℂ)) := by
        intro k
        dsimp [bcEulerTerm]
        rw [if_neg hn, if_neg hn]
        have harg :
            2 * Real.pi * Complex.I * (((r + k.1) / m : ℚ) : ℂ) * (n : ℂ) =
              2 * Real.pi * Complex.I * (((r / m : ℚ) : ℂ)) * (n : ℂ) +
                2 * Real.pi * Complex.I * (k.1 : ℂ) * (n : ℂ) / (m : ℂ) := by
          push_cast
          ring
        rw [harg, Complex.exp_add]
        ring
      simp_rw [hexp_split, ← Finset.mul_sum, finite_root_of_unity_sum m n]
      split_ifs with hdvd
      · ring
      · simp
  have htsum_inner :
      (∑' n : ℕ, ∑ k : Fin m, bcEulerTerm β σ ((r + k.1) / m) n) =
        ∑' n : ℕ, (if (m : ℕ) ∣ n then (m : ℂ) * bcEulerTerm β σ (r / m) n else 0) :=
    tsum_congr hinner_pt
  have hdvd_eq := tsum_ite_dvd_eq_tsum_mul m (fun n => (m : ℂ) * bcEulerTerm β σ (r / m) n)
  have hterm_scale : ∀ d : ℕ, (m : ℂ) * bcEulerTerm β σ (r / m) ((m : ℕ) * d) =
      (m : ℂ) * ((m : ℂ) ^ (-(β : ℂ)) * σ m * bcEulerTerm β σ r d) := by
    intro d
    by_cases hd0 : d = 0
    · subst hd0
      simp [bcEulerTerm]
    · have hmd0 : (m : ℕ) * d ≠ 0 := mul_ne_zero m.ne_zero hd0
      dsimp [bcEulerTerm]
      rw [if_neg hmd0, if_neg hd0]
      have hcp : (((m * d : ℕ) : ℂ) ^ (-(β : ℂ))) = (m : ℂ) ^ (-(β : ℂ)) * (d : ℂ) ^ (-(β : ℂ)) := by
        rw [Nat.cast_mul]
        simpa only [Complex.ofReal_natCast] using
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg (m : ℕ)) (Nat.cast_nonneg d) (-(β : ℂ))
      have hexp :
          Complex.exp (2 * Real.pi * Complex.I * (((r / m : ℚ) : ℂ)) * (((m * d : ℕ) : ℂ))) =
            Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (d : ℂ)) := by
        congr 1
        push_cast
        field_simp [hm_ne]
      rw [hcp, hσ_mul m d, hexp]
      ring
  have htsum_eq :
      ∑' n : ℕ, (if (m : ℕ) ∣ n then (m : ℂ) * bcEulerTerm β σ (r / m) n else 0) =
        ∑' d : ℕ, (m : ℂ) * ((m : ℂ) ^ (-(β : ℂ)) * σ m * bcEulerTerm β σ r d) := by
    rw [hdvd_eq]
    exact tsum_congr hterm_scale
  simp_rw [bcEulerCharacterState_eq_mul_tsum_term]
  rw [← Finset.mul_sum, hswap, htsum_inner, htsum_eq, tsum_mul_left, tsum_mul_left]
  exact complex_hecke_cancel (m : ℂ) (partitionSeries (β : ℂ))⁻¹
    ((m : ℂ) ^ (-(β : ℂ)) * σ m) (∑' d : ℕ, bcEulerTerm β σ r d) hm_ne

/-- Unconditionally satisfies the exact symmetric Bost–Connes Hecke-KMS recurrence for `σ = 1`. -/
theorem bcEulerCharacterState_one_hecke_recurrence
    {β : ℝ} (hβ : 1 < β) (m : ℕ+) (r : ℚ) :
    ((m : ℂ)⁻¹) * ∑ k : Fin m, bcEulerCharacterState β (fun _ => 1) ((r + k.1) / m) =
      ((m : ℂ) ^ (-(β : ℂ))) * bcEulerCharacterState β (fun _ => 1) r := by
  have h := bcEulerCharacterState_hecke_recurrence hβ (fun _ : ℕ => (1 : ℂ))
    (fun _ _ => by simp) (fun _ => by simp) m r
  simpa using h

end InfoGeometry.Arithmetic.BostConnesEulerProductKMSClassification
