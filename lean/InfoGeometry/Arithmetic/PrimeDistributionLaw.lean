import Mathlib

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

/-- Empirical prime density `π(N) / N`. -/
def empiricalPrimeDensity (N : ℕ) : ℝ :=
  (primeCounting N : ℝ) / (N : ℝ)

/-- The empirical density is normalized by the cutoff. -/
theorem empiricalPrimeDensity_mul_cutoff {N : ℕ} (hN : (N : ℝ) ≠ 0) :
    empiricalPrimeDensity N * (N : ℝ) = (primeCounting N : ℝ) := by
  unfold empiricalPrimeDensity
  field_simp [hN]

/-- The Cramer/PNT local-density heuristic `1 / log N`. -/
def logarithmicLocalDensity (N : ℕ) : ℝ :=
  1 / Real.log (N : ℝ)

/-- The PNT comparison scale `N / log N`. -/
def pntCountingScale (N : ℕ) : ℝ :=
  (N : ℝ) / Real.log (N : ℝ)

/-- Empirical PNT ratio `π(N) / (N / log N)`. -/
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

/-- Chebyshev `ψ` is nonnegative at every finite cutoff. -/
theorem chebyshevPsiFinite_nonneg (N : ℕ) :
    0 ≤ chebyshevPsiFinite N := by
  unfold chebyshevPsiFinite
  exact Finset.sum_nonneg fun n _hn => vonMangoldtWeight_nonneg n

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

/-- Residue-class prime sets are subsets of the prime cutoff. -/
theorem residuePrimeFinset_subset (N q a : ℕ) :
    residuePrimeFinset N q a ⊆ primesUpTo N := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

/-- A residue-class prime count is bounded by the total prime count. -/
theorem residuePrimeCount_le_primeCounting (N q a : ℕ) :
    residuePrimeCount N q a ≤ primeCounting N := by
  exact Finset.card_le_card (residuePrimeFinset_subset N q a)

/-- Empirical residue-class density among all integers up to cutoff `N`. -/
def residuePrimeDensity (N q a : ℕ) : ℝ :=
  (residuePrimeCount N q a : ℝ) / (N : ℝ)

/-- Empirical residue-class share among primes up to cutoff `N`. -/
def residuePrimeShare (N q a : ℕ) : ℝ :=
  (residuePrimeCount N q a : ℝ) / (primeCounting N : ℝ)

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
