import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Zeta.EvenLengthCorrection

open scoped BigOperators

namespace Omega.Zeta

/-- Fixed-parameter necklace correction kernel.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
def necklaceCorrectionKernel (v n : Nat) : Int :=
  if Even n then
    Finset.sum (Nat.divisors (n / 2)) (fun d => ArithmeticFunction.moebius d * (v : Int) ^ ((n / 2) / d))
  else 0

/-- Odd lengths contribute zero to the necklace correction kernel.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_odd (v n : Nat) (hn : ¬ Even n) :
    necklaceCorrectionKernel v n = 0 := by
  simp [necklaceCorrectionKernel, hn]

/-- Even lengths reduce to the divisor-sum correction formula.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_even (v m : Nat) :
    necklaceCorrectionKernel v (2 * m) =
      Finset.sum (Nat.divisors m) (fun d => ArithmeticFunction.moebius d * (v : Int) ^ (m / d)) := by
  simp [necklaceCorrectionKernel]

private theorem moebius_one_value : ArithmeticFunction.moebius 1 = 1 := by
  exact ArithmeticFunction.moebius_apply_one

private theorem moebius_two_value : ArithmeticFunction.moebius 2 = -1 := by
  simpa using (ArithmeticFunction.moebius_apply_prime (p := 2) (by norm_num))

private theorem moebius_three_value : ArithmeticFunction.moebius 3 = -1 := by
  simpa using (ArithmeticFunction.moebius_apply_prime (p := 3) (by norm_num))

private theorem moebius_four_value : ArithmeticFunction.moebius 4 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsf
  have h := (Nat.squarefree_iff_prime_squarefree.mp hsf) 2 Nat.prime_two
  norm_num at h

private theorem moebius_five_value : ArithmeticFunction.moebius 5 = -1 := by
  simpa using (ArithmeticFunction.moebius_apply_prime (p := 5) (by norm_num))

private theorem moebius_six_value : ArithmeticFunction.moebius 6 = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree]
  · norm_num [ArithmeticFunction.cardFactors_apply, Nat.primeFactorsList]
  · rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
    norm_num [Nat.primeFactorsList]

private theorem divisors_one_value : Nat.divisors 1 = {1} := by
  norm_num [Nat.divisors]

private theorem divisors_two_value : Nat.divisors 2 = {1, 2} := by
  simpa using (Nat.Prime.divisors (by norm_num : Nat.Prime 2))

private theorem divisors_three_value : Nat.divisors 3 = {1, 3} := by
  simpa using (Nat.Prime.divisors (by norm_num : Nat.Prime 3))

private theorem divisors_four_value : Nat.divisors 4 = {1, 2, 4} := by
  change Nat.divisors (2 ^ 2) = {1, 2, 4}
  rw [Nat.divisors_prime_pow (p := 2) (by norm_num : Nat.Prime 2) 2]
  norm_num [Finset.map, Finset.range]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_mk,
    Multiset.mem_singleton]
  tauto

private theorem divisors_five_value : Nat.divisors 5 = {1, 5} := by
  simpa using (Nat.Prime.divisors (by norm_num : Nat.Prime 5))

private theorem divisors_six_value : Nat.divisors 6 = {1, 2, 3, 6} := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hdvd, _⟩
    have hdvd' : d ∣ 2 * 3 := by simpa using hdvd
    obtain ⟨a, b, ha, hb, heq⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd'
    have ha_cases : a = 1 ∨ a = 2 := (Nat.dvd_prime (by norm_num)).mp ha
    have hb_cases : b = 1 ∨ b = 3 := (Nat.dvd_prime (by norm_num)).mp hb
    rw [heq] at ⊢
    rcases ha_cases with rfl | rfl
    · rcases hb_cases with rfl | rfl
      · exact Or.inl (by norm_num)
      · exact Or.inr (Or.inr (Or.inl (by norm_num)))
    · rcases hb_cases with rfl | rfl
      · exact Or.inr (Or.inl (by norm_num))
      · exact Or.inr (Or.inr (Or.inr (by norm_num)))
  · rintro (rfl | rfl | rfl | rfl)
    · norm_num
    · norm_num
    · norm_num
    · norm_num

private theorem necklaceCorrectionKernel_v2_2 : necklaceCorrectionKernel 2 2 = 2 := by
  change necklaceCorrectionKernel 2 (2 * 1) = 2
  rw [necklaceCorrectionKernel_even, divisors_one_value]
  simp

private theorem necklaceCorrectionKernel_v2_4 : necklaceCorrectionKernel 2 4 = 2 := by
  change necklaceCorrectionKernel 2 (2 * 2) = 2
  rw [necklaceCorrectionKernel_even, divisors_two_value]
  norm_num [moebius_one_value, moebius_two_value]

private theorem necklaceCorrectionKernel_v2_6 : necklaceCorrectionKernel 2 6 = 6 := by
  change necklaceCorrectionKernel 2 (2 * 3) = 6
  rw [necklaceCorrectionKernel_even, divisors_three_value]
  norm_num [moebius_one_value, moebius_three_value]

private theorem necklaceCorrectionKernel_v2_8 : necklaceCorrectionKernel 2 8 = 12 := by
  change necklaceCorrectionKernel 2 (2 * 4) = 12
  rw [necklaceCorrectionKernel_even, divisors_four_value]
  norm_num [moebius_one_value, moebius_two_value, moebius_four_value]

private theorem necklaceCorrectionKernel_v2_10 : necklaceCorrectionKernel 2 10 = 30 := by
  change necklaceCorrectionKernel 2 (2 * 5) = 30
  rw [necklaceCorrectionKernel_even, divisors_five_value]
  norm_num [moebius_one_value, moebius_five_value]

private theorem necklaceCorrectionKernel_v2_12 : necklaceCorrectionKernel 2 12 = 54 := by
  change necklaceCorrectionKernel 2 (2 * 6) = 54
  rw [necklaceCorrectionKernel_even, divisors_six_value]
  norm_num [moebius_one_value, moebius_two_value,
    moebius_three_value, moebius_six_value]

/-- Every odd successor length has zero correction.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_odd_eq_zero (v m : Nat) :
    necklaceCorrectionKernel v (2 * m + 1) = 0 := by
  simp [necklaceCorrectionKernel]

/-- Unified divisor form of the necklace correction kernel.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_divisor_form (v n : Nat) :
    necklaceCorrectionKernel v n =
      Finset.sum ((Nat.divisors n).filter (fun d => Even (n / d)))
        (fun d => ArithmeticFunction.moebius d * (v : Int) ^ ((n / d) / 2)) := by
  by_cases hn : Even n
  · rcases hn with ⟨m, hm⟩
    rw [hm, show m + m = 2 * m by omega, necklaceCorrectionKernel_even]
    have hfilter :
        (Nat.divisors (2 * m)).filter (fun d => Even ((2 * m) / d)) = Nat.divisors m := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdvd, hne⟩, hEven⟩
        refine ⟨?_, by omega⟩
        rcases hEven with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hmul : d * ((2 * m) / d) = d * (k + k) := by rw [hk]
        have hmul' : 2 * m = d * (k + k) := by
          calc
            2 * m = d * ((2 * m) / d) := (Nat.mul_div_cancel' hdvd).symm
            _ = d * (k + k) := hmul
        have hmul'' : 2 * m = 2 * (d * k) := by
          calc
            2 * m = d * (k + k) := hmul'
            _ = d * k + d * k := by rw [Nat.mul_add]
            _ = 2 * (d * k) := by rw [← two_mul]
        exact Nat.eq_of_mul_eq_mul_left (by omega) hmul''
      · rintro ⟨hdvd, hmne⟩
        refine ⟨?_, ?_⟩
        · exact ⟨dvd_mul_of_dvd_right hdvd 2, by omega⟩
        · rcases hdvd with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          have hdne : d ≠ 0 := by
            intro hd0
            subst hd0
            have hm0 : m = 0 := by simpa using hk
            exact hmne hm0
          rw [hk]
          calc
            (2 * (d * k)) / d = ((2 * k) * d) / d := by ring_nf
            _ = 2 * k := by
              have hq : d * (2 * k) / d = 2 * k := Nat.mul_div_right (2 * k) (Nat.pos_of_ne_zero hdne)
              simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hq
            _ = k + k := by rw [two_mul]
    rw [hfilter]
    refine Finset.sum_congr rfl ?_
    intro d hd
    have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hhalf : (m / d) * 2 / 2 = m / d := by
      rw [Nat.mul_comm, Nat.mul_div_right _ (by decide)]
    rw [Nat.mul_div_assoc 2 hdvd, show 2 * (m / d) = (m / d) * 2 by rw [Nat.mul_comm], hhalf]
  · rw [necklaceCorrectionKernel_odd v n hn]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    have hdmem : d ∈ (Nat.divisors n).filter (fun d => Even (n / d)) := by simpa using hd
    exfalso
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdmem).1
    have hEven : Even (n / d) := (Finset.mem_filter.mp hdmem).2
    apply hn
    rcases hEven with ⟨k, hk⟩
    refine ⟨d * k, ?_⟩
    calc
      n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
      _ = d * (k + k) := by rw [hk]
      _ = d * k + d * k := by rw [Nat.mul_add]
      _ = 2 * (d * k) := by rw [← two_mul]
      _ = d * k + d * k := by rw [two_mul]

/-- Necklace correction kernel vanishes at odd lengths.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem paper_necklaceCorrectionKernel_odd_zero :
    (∀ v m : Nat, necklaceCorrectionKernel v (2 * m + 1) = 0) ∧
    necklaceCorrectionKernel 2 2 = 2 ∧
    necklaceCorrectionKernel 2 4 = 2 ∧
    necklaceCorrectionKernel 2 6 = 6 :=
  ⟨necklaceCorrectionKernel_odd_eq_zero, necklaceCorrectionKernel_v2_2,
   necklaceCorrectionKernel_v2_4, necklaceCorrectionKernel_v2_6⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R301: Necklace correction kernel extended values
-- ══════════════════════════════════════════════════════════════

/-- Necklace correction kernel extended values for v=2.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_values_extended :
    necklaceCorrectionKernel 2 8 = 12 ∧
    necklaceCorrectionKernel 2 10 = 30 ∧
    necklaceCorrectionKernel 2 12 = 54 := by
  exact ⟨necklaceCorrectionKernel_v2_8, necklaceCorrectionKernel_v2_10,
    necklaceCorrectionKernel_v2_12⟩

/-- Necklace correction kernel values for v=3 (ternary).
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_ternary :
    necklaceCorrectionKernel 3 2 = 3 ∧
    necklaceCorrectionKernel 3 4 = 6 ∧
    necklaceCorrectionKernel 3 6 = 24 := by
  constructor
  · change necklaceCorrectionKernel 3 (2 * 1) = 3
    rw [necklaceCorrectionKernel_even, divisors_one_value]
    simp
  · constructor
    · change necklaceCorrectionKernel 3 (2 * 2) = 6
      rw [necklaceCorrectionKernel_even, divisors_two_value]
      norm_num [moebius_one_value, moebius_two_value]
    · change necklaceCorrectionKernel 3 (2 * 3) = 24
      rw [necklaceCorrectionKernel_even, divisors_three_value]
      norm_num [moebius_one_value, moebius_three_value]

/-- Paper package.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem paper_necklaceCorrectionKernel_extended :
    (∀ v m : Nat, necklaceCorrectionKernel v (2 * m + 1) = 0) ∧
    necklaceCorrectionKernel 2 8 = 12 ∧
    necklaceCorrectionKernel 2 10 = 30 ∧
    necklaceCorrectionKernel 2 12 = 54 ∧
    necklaceCorrectionKernel 3 2 = 3 ∧
    necklaceCorrectionKernel 3 4 = 6 ∧
    necklaceCorrectionKernel 3 6 = 24 :=
  ⟨necklaceCorrectionKernel_odd_eq_zero,
   necklaceCorrectionKernel_v2_8, necklaceCorrectionKernel_v2_10,
   necklaceCorrectionKernel_v2_12,
   (necklaceCorrectionKernel_ternary).1,
   (necklaceCorrectionKernel_ternary).2.1,
   (necklaceCorrectionKernel_ternary).2.2⟩

/-- Necklace correction at v=2 for small even values.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem paper_necklace_correction_two_values :
    necklaceCorrectionKernel 2 2 = 2 ∧
    necklaceCorrectionKernel 2 4 = 2 ∧
    necklaceCorrectionKernel 2 6 = 6 ∧
    necklaceCorrectionKernel 2 8 = 12 ∧
    necklaceCorrectionKernel 2 10 = 30 ∧
    necklaceCorrectionKernel 2 12 = 54 := by
  exact ⟨necklaceCorrectionKernel_v2_2, necklaceCorrectionKernel_v2_4,
    necklaceCorrectionKernel_v2_6, necklaceCorrectionKernel_v2_8,
    necklaceCorrectionKernel_v2_10, necklaceCorrectionKernel_v2_12⟩

/-- Necklace correction at v=2 is positive for 1 ≤ m ≤ 6.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_at_two_pos_small :
    ∀ m, 1 ≤ m → m ≤ 6 → 0 < necklaceCorrectionKernel 2 (2 * m) := by
  intro m hm hm'
  have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 := by omega
  rcases hm_cases with hm | hm | hm | hm | hm | hm
  · subst m
    simpa using (show 0 < necklaceCorrectionKernel 2 2 by
      rw [necklaceCorrectionKernel_v2_2]; norm_num)
  · subst m
    simpa using (show 0 < necklaceCorrectionKernel 2 4 by
      rw [necklaceCorrectionKernel_v2_4]; norm_num)
  · subst m
    simpa using (show 0 < necklaceCorrectionKernel 2 6 by
      rw [necklaceCorrectionKernel_v2_6]; norm_num)
  · subst m
    simpa using (show 0 < necklaceCorrectionKernel 2 8 by
      rw [necklaceCorrectionKernel_v2_8]; norm_num)
  · subst m
    simpa using (show 0 < necklaceCorrectionKernel 2 10 by
      rw [necklaceCorrectionKernel_v2_10]; norm_num)
  · subst m
    simpa using (show 0 < necklaceCorrectionKernel 2 12 by
      rw [necklaceCorrectionKernel_v2_12]; norm_num)

/-- At prime m=p: E(v,2p) - N(v,2p) = v^p + v.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem evenLength_sub_necklace_at_prime (v : Nat) {p : Nat} (hp : Nat.Prime p) :
    (evenLengthCorrection v (2 * p) : ℤ) - necklaceCorrectionKernel v (2 * p) =
    (v : ℤ) ^ p + v := by
  rw [evenLengthCorrection_even, necklaceCorrectionKernel_even]
  -- E = 2·v^p, N = Σ_{d|p} μ(d)·v^(p/d)
  -- divisors p = {1, p} for prime p
  have hDivs : Nat.divisors p = {1, p} := by
    ext d; simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ⟨hd, hne⟩; exact (Nat.dvd_prime hp).mp hd
    · rintro (rfl | rfl) <;> simp [hp.ne_zero]
  rw [hDivs, Finset.sum_insert (show (1 : ℕ) ∉ ({p} : Finset ℕ) from by
    simp; exact hp.ne_one.symm), Finset.sum_singleton]
  rw [Nat.div_one, Nat.div_self hp.pos]
  have hμ1 : ArithmeticFunction.moebius 1 = (1 : ℤ) := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree (by simp)]; norm_num
  have hμp : ArithmeticFunction.moebius p = (-1 : ℤ) := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hp.squarefree,
      ArithmeticFunction.cardFactors_apply_prime hp, pow_one]
  rw [hμ1, hμp]; push_cast; ring

-- Phase R604: Necklace correction kernel v=2 seeds
-- ══════════════════════════════════════════════════════════════

/-- Extended v=2 seeds including n=8,10,12.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_v2_seeds :
    necklaceCorrectionKernel 2 2 = 2 ∧
    necklaceCorrectionKernel 2 4 = 2 ∧
    necklaceCorrectionKernel 2 6 = 6 ∧
    necklaceCorrectionKernel 2 8 = 12 ∧
    necklaceCorrectionKernel 2 10 = 30 ∧
    necklaceCorrectionKernel 2 12 = 54 := by
  exact ⟨necklaceCorrectionKernel_v2_2, necklaceCorrectionKernel_v2_4,
    necklaceCorrectionKernel_v2_6, necklaceCorrectionKernel_v2_8,
    necklaceCorrectionKernel_v2_10, necklaceCorrectionKernel_v2_12⟩

/-- Necklace number = kernel / v for v=2.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem necklaceCorrectionKernel_v2_necklace_number :
    necklaceCorrectionKernel 2 2 / 2 = 1 ∧
    necklaceCorrectionKernel 2 4 / 2 = 1 ∧
    necklaceCorrectionKernel 2 6 / 2 = 3 ∧
    necklaceCorrectionKernel 2 8 / 2 = 6 := by
  rw [necklaceCorrectionKernel_v2_2, necklaceCorrectionKernel_v2_4,
    necklaceCorrectionKernel_v2_6, necklaceCorrectionKernel_v2_8]
  norm_num

/-- Golden-mean necklace correction seeds: even values and odd zeros.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem paper_necklace_correction_golden_mean_seeds :
    necklaceCorrectionKernel 2 2 = 2 ∧
    necklaceCorrectionKernel 2 4 = 2 ∧
    necklaceCorrectionKernel 2 6 = 6 ∧
    necklaceCorrectionKernel 2 1 = 0 ∧
    necklaceCorrectionKernel 2 3 = 0 ∧
    necklaceCorrectionKernel 2 5 = 0 := by
  exact ⟨necklaceCorrectionKernel_v2_2, necklaceCorrectionKernel_v2_4,
    necklaceCorrectionKernel_v2_6,
    necklaceCorrectionKernel_odd_eq_zero 2 0,
    necklaceCorrectionKernel_odd_eq_zero 2 1,
    necklaceCorrectionKernel_odd_eq_zero 2 2⟩

end Omega.Zeta
