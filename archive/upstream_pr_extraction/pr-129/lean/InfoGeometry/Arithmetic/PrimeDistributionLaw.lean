import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# InfoGeometry.Arithmetic.PrimeDistributionLaw

Finite and asymptotic prime-distribution observables.

This file separates two layers:

* **proved finite bookkeeping:** prime cutoffs, empirical densities,
  Chebyshev `θ`/`ψ` readouts, residue-class counts, monotonicity, and
  nonnegativity;
* **analytic/asymptotic law packets:** PNT, Chebyshev `ψ(x) ~ x`,
  residue-class equidistribution, and RH-style error bounds are recorded as
  explicit propositions/structures.

No Prime Number Theorem, RH, or Hardy--Littlewood theorem is proved here.
-/

noncomputable section

open scoped BigOperators
open Filter Topology

namespace InfoGeometry.Arithmetic.PrimeDistributionLaw

/-! ## Finite empirical prime observables -/

/-- Prime numbers at or below the finite cutoff `N`. -/
def primesUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime

/-- Prime-counting function at a finite cutoff. -/
def primeCounting (N : ℕ) : ℕ :=
  (primesUpTo N).card

/-- Membership in the prime cutoff is exactly primality plus `p ≤ N`. -/
theorem mem_primesUpTo_iff {p N : ℕ} :
    p ∈ primesUpTo N ↔ p ≤ N ∧ Nat.Prime p := by
  simp [primesUpTo]

/-- All elements of `primesUpTo N` are prime. -/
theorem prime_of_mem_primesUpTo {p N : ℕ} (hp : p ∈ primesUpTo N) :
    Nat.Prime p :=
  (mem_primesUpTo_iff.mp hp).2

/-- All elements of `primesUpTo N` are bounded by the cutoff. -/
theorem le_cutoff_of_mem_primesUpTo {p N : ℕ} (hp : p ∈ primesUpTo N) :
    p ≤ N :=
  (mem_primesUpTo_iff.mp hp).1

/-- Prime cutoff sets are monotone in the cutoff. -/
theorem primesUpTo_subset_of_le {M N : ℕ} (hMN : M ≤ N) :
    primesUpTo M ⊆ primesUpTo N := by
  intro p hp
  rw [mem_primesUpTo_iff] at hp ⊢
  exact ⟨le_trans hp.1 hMN, hp.2⟩

/-- Prime counting is monotone in the cutoff. -/
theorem primeCounting_monotone {M N : ℕ} (hMN : M ≤ N) :
    primeCounting M ≤ primeCounting N := by
  exact Finset.card_le_card (primesUpTo_subset_of_le hMN)

/-- There are no primes at cutoff `0`. -/
theorem primeCounting_zero :
    primeCounting 0 = 0 := by
  simp [primeCounting, primesUpTo, Nat.not_prime_zero]

theorem primeCounting_le_cutoff_succ (N : ℕ) :
    primeCounting N ≤ N + 1 := by
  unfold primeCounting primesUpTo
  simpa using
    (Finset.card_filter_le (Finset.range (N + 1)) (p := Nat.Prime))

theorem primeCounting_pos_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    0 < primeCounting N := by
  have h2 : 2 ∈ primesUpTo N := by
    rw [mem_primesUpTo_iff]
    exact ⟨hN, Nat.prime_two⟩
  exact Finset.card_pos.mpr ⟨2, h2⟩

theorem primeCounting_cast_ne_zero_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    (primeCounting N : ℝ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (primeCounting_pos_of_two_le hN))

/-- Empirical prime density `π(N) / N`. -/
def empiricalPrimeDensity (N : ℕ) : ℝ :=
  (primeCounting N : ℝ) / (N : ℝ)

/-- The empirical density is normalized by the cutoff. -/
theorem empiricalPrimeDensity_mul_cutoff {N : ℕ} (hN : (N : ℝ) ≠ 0) :
    empiricalPrimeDensity N * (N : ℝ) = (primeCounting N : ℝ) := by
  unfold empiricalPrimeDensity
  field_simp [hN]

/-- The logarithmic comparison scale `1 / log N`. -/
def logarithmicLocalDensity (N : ℕ) : ℝ :=
  1 / Real.log (N : ℝ)

/-- The finite comparison scale `N / log N`. -/
def pntCountingScale (N : ℕ) : ℝ :=
  (N : ℝ) / Real.log (N : ℝ)

/-- The empirical ratio `π(N) / (N / log N)`. -/
def pntCountingRatio (N : ℕ) : ℝ :=
  (primeCounting N : ℝ) / pntCountingScale N

/-! ## Chebyshev/von Mangoldt readouts -/

/-- Real-valued von Mangoldt weight. -/
def vonMangoldtWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

/-- Chebyshev `θ(N) = Σ_{p ≤ N} log p`. -/
def chebyshevThetaFinite (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, Real.log (p : ℝ)

/-- Chebyshev `ψ(N) = Σ_{n ≤ N} Λ(n)` in finite cutoff form. -/
def chebyshevPsiFinite (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), vonMangoldtWeight n

/-- Von Mangoldt weights are nonnegative. -/
theorem vonMangoldtWeight_nonneg (n : ℕ) :
    0 ≤ vonMangoldtWeight n := by
  simp [vonMangoldtWeight, ArithmeticFunction.vonMangoldt_nonneg]

/-- At a prime, the von Mangoldt weight is `log p`. -/
theorem vonMangoldtWeight_apply_prime {p : ℕ} (hp : Nat.Prime p) :
    vonMangoldtWeight p = Real.log (p : ℝ) := by
  simpa [vonMangoldtWeight] using ArithmeticFunction.vonMangoldt_apply_prime hp

/-- The logarithmic prime weight is nonnegative. -/
theorem log_nat_prime_nonneg {p : ℕ} (hp : Nat.Prime p) :
    0 ≤ Real.log (p : ℝ) := by
  have hp_one : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.Prime.one_lt hp).le
  exact Real.log_nonneg hp_one

/-- Chebyshev `θ` is nonnegative at every finite cutoff. -/
theorem chebyshevThetaFinite_nonneg (N : ℕ) :
    0 ≤ chebyshevThetaFinite N := by
  unfold chebyshevThetaFinite
  exact Finset.sum_nonneg fun p hp => log_nat_prime_nonneg (prime_of_mem_primesUpTo hp)

theorem chebyshevThetaFinite_monotone {M N : ℕ} (hMN : M ≤ N) :
    chebyshevThetaFinite M ≤ chebyshevThetaFinite N := by
  unfold chebyshevThetaFinite
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (primesUpTo_subset_of_le hMN)
  intro p hp _hnot
  exact log_nat_prime_nonneg (prime_of_mem_primesUpTo hp)

/-- Chebyshev `ψ` is nonnegative at every finite cutoff. -/
theorem chebyshevPsiFinite_nonneg (N : ℕ) :
    0 ≤ chebyshevPsiFinite N := by
  unfold chebyshevPsiFinite
  exact Finset.sum_nonneg fun n _hn => vonMangoldtWeight_nonneg n

theorem chebyshevPsiFinite_monotone {M N : ℕ} (hMN : M ≤ N) :
    chebyshevPsiFinite M ≤ chebyshevPsiFinite N := by
  unfold chebyshevPsiFinite
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hn) (Nat.succ_le_succ hMN))
  · intro n _hn _hnot
    exact vonMangoldtWeight_nonneg n

/-- Chebyshev `θ` density `θ(N) / N`. -/
def chebyshevThetaDensity (N : ℕ) : ℝ :=
  chebyshevThetaFinite N / (N : ℝ)

/-- Chebyshev `ψ` density `ψ(N) / N`. -/
def chebyshevPsiDensity (N : ℕ) : ℝ :=
  chebyshevPsiFinite N / (N : ℝ)

/-! ## Residue-class empirical counts -/

/-- Prime cutoff restricted to one residue class modulo `q`. -/
def residuePrimeFinset (N q a : ℕ) : Finset ℕ :=
  (primesUpTo N).filter fun p => p % q = a % q

/-- Count of primes at cutoff `N` in residue class `a mod q`. -/
def residuePrimeCount (N q a : ℕ) : ℕ :=
  (residuePrimeFinset N q a).card

theorem residuePrimeCount_zero (q a : ℕ) :
    residuePrimeCount 0 q a = 0 := by
  have hzero : ¬Nat.Prime 0 := Nat.not_prime_zero
  simp [residuePrimeCount, residuePrimeFinset, primesUpTo, hzero]

/-- Residue-class prime sets are subsets of the prime cutoff. -/
theorem residuePrimeFinset_subset (N q a : ℕ) :
    residuePrimeFinset N q a ⊆ primesUpTo N := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

/-- A residue-class prime count is bounded by the total prime count. -/
theorem residuePrimeCount_le_primeCounting (N q a : ℕ) :
    residuePrimeCount N q a ≤ primeCounting N := by
  exact Finset.card_le_card (residuePrimeFinset_subset N q a)

theorem residuePrimeCount_monotone {M N q a : ℕ} (hMN : M ≤ N) :
    residuePrimeCount M q a ≤ residuePrimeCount N q a := by
  apply Finset.card_le_card
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  exact ⟨primesUpTo_subset_of_le hMN hp'.1, hp'.2⟩

/-- Empirical residue-class density among all integers up to cutoff `N`. -/
def residuePrimeDensity (N q a : ℕ) : ℝ :=
  (residuePrimeCount N q a : ℝ) / (N : ℝ)

theorem residuePrimeDensity_nonneg (N q a : ℕ) :
    0 ≤ residuePrimeDensity N q a := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem residuePrimeDensity_mul_cutoff {N q a : ℕ}
    (hN : (N : ℝ) ≠ 0) :
    residuePrimeDensity N q a * (N : ℝ) = (residuePrimeCount N q a : ℝ) := by
  unfold residuePrimeDensity
  field_simp [hN]

theorem residuePrimeDensity_eq_zero_iff_count_eq_zero {N q a : ℕ}
    (hN : 0 < N) :
    residuePrimeDensity N q a = 0 ↔ residuePrimeCount N q a = 0 := by
  unfold residuePrimeDensity
  have hden : (N : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hN)
  rw [div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact_mod_cast h
    · exact (hden h).elim
  · intro h
    exact Or.inl (by exact_mod_cast h)

/-- Empirical residue-class share among primes up to cutoff `N`. -/
def residuePrimeShare (N q a : ℕ) : ℝ :=
  (residuePrimeCount N q a : ℝ) / (primeCounting N : ℝ)

theorem residuePrimeShare_nonneg (N q a : ℕ) :
    0 ≤ residuePrimeShare N q a := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem residuePrimeShare_mul_primeCounting {N q a : ℕ}
    (hN : (primeCounting N : ℝ) ≠ 0) :
    residuePrimeShare N q a * (primeCounting N : ℝ) =
      (residuePrimeCount N q a : ℝ) := by
  unfold residuePrimeShare
  field_simp [hN]

theorem residuePrimeShare_le_one {N q a : ℕ} (hN : 2 ≤ N) :
    residuePrimeShare N q a ≤ 1 := by
  have hden : (0 : ℝ) < primeCounting N := by
    exact_mod_cast primeCounting_pos_of_two_le hN
  unfold residuePrimeShare
  rw [div_le_iff₀ hden]
  simpa using (show (residuePrimeCount N q a : ℝ) ≤
      (primeCounting N : ℝ) by
    exact_mod_cast residuePrimeCount_le_primeCounting N q a)

theorem residuePrimeShare_pos_of_count_pos {N q a : ℕ}
    (hN : 2 ≤ N) (hcount : 0 < residuePrimeCount N q a) :
    0 < residuePrimeShare N q a := by
  unfold residuePrimeShare
  apply div_pos
  · exact_mod_cast hcount
  · exact_mod_cast primeCounting_pos_of_two_le hN

theorem residuePrimeShare_eq_zero_iff_count_eq_zero {N q a : ℕ}
    (hN : 2 ≤ N) :
    residuePrimeShare N q a = 0 ↔ residuePrimeCount N q a = 0 := by
  unfold residuePrimeShare
  have hden : (primeCounting N : ℝ) ≠ 0 :=
    primeCounting_cast_ne_zero_of_two_le hN
  rw [div_eq_zero_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact_mod_cast h
    · exact (hden h).elim
  · intro h
    exact Or.inl (by exact_mod_cast h)

/-! ## Explicit asymptotic law packets -/

/--
Asymptotic equivalence at infinity, encoded by ratio convergence to `1`.

This is a predicate, not a proof.  It lets downstream files state exactly which
analytic asymptotic law they are assuming.
-/
def AsymptoticEquivalentAtTop (f g : ℕ → ℝ) : Prop :=
  Tendsto (fun N : ℕ => f N / g N) atTop (nhds (1 : ℝ))

/-- Prime Number Theorem in prime-counting form: `π(N) ~ N / log N`. -/
def PrimeNumberTheoremCountingLaw : Prop :=
  AsymptoticEquivalentAtTop
    (fun N => (primeCounting N : ℝ))
    pntCountingScale

/-- Chebyshev/von Mangoldt form of PNT: `ψ(N) ~ N`. -/
def ChebyshevPsiAsymptoticLaw : Prop :=
  AsymptoticEquivalentAtTop
    chebyshevPsiFinite
    (fun N => (N : ℝ))

/-- Theta form of PNT: `θ(N) ~ N`. -/
def ChebyshevThetaAsymptoticLaw : Prop :=
  AsymptoticEquivalentAtTop
    chebyshevThetaFinite
    (fun N => (N : ℝ))

/--
Residue-class equidistribution law for a fixed modulus.

For every pair of reduced residue classes, their prime counts are
asymptotically equivalent.  This avoids baking in a particular `φ(q)` API while
still expressing the empirical/Dirichlet equidistribution content.
-/
def ResidueEquidistributionLaw (q : ℕ) : Prop :=
  ∀ a b : ℕ,
    Nat.Coprime a q →
    Nat.Coprime b q →
      AsymptoticEquivalentAtTop
        (fun N => (residuePrimeCount N q a : ℝ))
        (fun N => (residuePrimeCount N q b : ℝ))

/--
RH-style square-root error law for prime counting.

This is intentionally a supplied analytic bound, not a theorem proved here.
-/
def RHPrimeCountingErrorLaw : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 2 ≤ N →
      |(primeCounting N : ℝ) - pntCountingScale N| ≤
        C * Real.sqrt (N : ℝ) * Real.log (N : ℝ)

end InfoGeometry.Arithmetic.PrimeDistributionLaw
