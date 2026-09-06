import Mathlib
import proofs.IJIRTRiemannDigest

/-!
# Misra prime-entropy digest

Formal digest of Alec Misra's *Entropy and Prime Number Distribution; (a
Non-heuristic Approach)*.

The finite arithmetic around the proposed entropy proxy `x / π(x)` is proved.
The paper's large claims (RH, `P ≠ NP`, twin primes) are represented only as
neutral Type-valued parameters, not as proved propositions.  In particular, the
convention that `1` is prime-like is named `MisraPrimeLike`; it is not Lean's
`Nat.Prime`.
-/

noncomputable section

namespace MisraPrimeEntropyDigest

/-- Misra's nonstandard prime-like convention: `1` is counted as the base
entropy unit, alongside ordinary primes. -/
def MisraPrimeLike (n : ℕ) : Prop := n = 1 ∨ Nat.Prime n

instance (n : ℕ) : Decidable (MisraPrimeLike n) := by
  unfold MisraPrimeLike
  infer_instance

/-- Prime-counting function with Misra's additional `1` convention. -/
def piOne (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter MisraPrimeLike).card

/-- Misra's dimensionless finite entropy proxy `E₁(n)=n/π₁(n)`. -/
def misraEntropy (n : ℕ) : ℚ :=
  (n : ℚ) / (piOne n : ℚ)

/-- Ordinary Lean primality still excludes `1`. -/
theorem one_not_natPrime : ¬ Nat.Prime 1 := by
  norm_num [Nat.Prime]

/-- Under Misra's convention, `1` is prime-like. -/
theorem one_misraPrimeLike : MisraPrimeLike 1 := by
  left
  rfl

/-- Exact finite counts cited by the paper. -/
theorem piOne_small_values :
    piOne 1 = 1 ∧
    piOne 10 = 5 ∧
    piOne 11 = 6 ∧
    piOne 12 = 6 ∧
    piOne 13 = 7 ∧
    piOne 14 = 7 := by
  have h1 : (Finset.range 2).filter MisraPrimeLike = ({1} : Finset ℕ) := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      have hxlt : x < 2 := hx.1
      interval_cases x
      all_goals simp [MisraPrimeLike] at hx ⊢
      all_goals norm_num at hx
    · intro hx
      simp at hx
      rcases hx with rfl
      norm_num [MisraPrimeLike]
  have h10 :
      (Finset.range 11).filter MisraPrimeLike = ({1, 2, 3, 5, 7} : Finset ℕ) := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      have hxlt : x < 11 := hx.1
      interval_cases x
      all_goals simp [MisraPrimeLike] at hx ⊢
      all_goals norm_num at hx
    · intro hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> norm_num [MisraPrimeLike]
  have h11 :
      (Finset.range 12).filter MisraPrimeLike = ({1, 2, 3, 5, 7, 11} : Finset ℕ) := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      have hxlt : x < 12 := hx.1
      interval_cases x
      all_goals simp [MisraPrimeLike] at hx ⊢
      all_goals norm_num at hx
    · intro hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [MisraPrimeLike]
  have h12 :
      (Finset.range 13).filter MisraPrimeLike = ({1, 2, 3, 5, 7, 11} : Finset ℕ) := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      have hxlt : x < 13 := hx.1
      interval_cases x
      all_goals simp [MisraPrimeLike] at hx ⊢
      all_goals norm_num at hx
    · intro hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [MisraPrimeLike]
  have h13 :
      (Finset.range 14).filter MisraPrimeLike = ({1, 2, 3, 5, 7, 11, 13} : Finset ℕ) := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      have hxlt : x < 14 := hx.1
      interval_cases x
      all_goals simp [MisraPrimeLike] at hx ⊢
      all_goals norm_num at hx
    · intro hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [MisraPrimeLike]
  have h14 :
      (Finset.range 15).filter MisraPrimeLike = ({1, 2, 3, 5, 7, 11, 13} : Finset ℕ) := by
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      have hxlt : x < 15 := hx.1
      interval_cases x
      all_goals simp [MisraPrimeLike] at hx ⊢
      all_goals norm_num at hx
    · intro hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [MisraPrimeLike]
  unfold piOne
  norm_num [h1, h10, h11, h12, h13, h14]

/-- Exact finite entropy values cited by the paper. -/
theorem entropy_small_values :
    misraEntropy 1 = 1 ∧
    misraEntropy 10 = 2 ∧
    misraEntropy 11 = 11 / 6 ∧
    misraEntropy 12 = 2 ∧
    misraEntropy 13 = 13 / 7 ∧
    misraEntropy 14 = 2 := by
  rcases piOne_small_values with ⟨h1, h10, h11, h12, h13, h14⟩
  unfold misraEntropy
  norm_num [h1, h10, h11, h12, h13, h14]

/-- The finite “entropy reversal” example: the entropy proxy decreases from
`10` to the new prime-like point `11`. -/
theorem entropy_reversal_10_11 :
    misraEntropy 11 < misraEntropy 10 := by
  rcases piOne_small_values with ⟨_, h10, h11, _, _, _⟩
  unfold misraEntropy
  norm_num [h10, h11]

/-- Entropy assonance example from the paper: `10`, `12`, and `14` have the
same proxy value under the `π₁` convention. -/
theorem entropy_assonance_10_12_14 :
    misraEntropy 10 = misraEntropy 12 ∧ misraEntropy 12 = misraEntropy 14 := by
  rcases piOne_small_values with ⟨_, h10, _, h12, _, h14⟩
  unfold misraEntropy
  norm_num [h10, h12, h14]

/-- The nonstandard prime-like count is the ordinary prime count plus one once
`n ≥ 1`. -/
theorem piOne_ordinary_shift (n : ℕ) (hn : 1 ≤ n) :
    piOne n = ((Finset.range (n + 1)).filter Nat.Prime).card + 1 := by
  unfold piOne
  let s : Finset ℕ := Finset.range (n + 1)
  have hn0 : 0 < n := hn
  have hset : s.filter MisraPrimeLike = insert 1 (s.filter Nat.Prime) := by
    ext x
    by_cases hx1 : x = 1
    · subst x
      simp [s, MisraPrimeLike, hn0]
    · simp [s, MisraPrimeLike, hx1]
  rw [hset]
  have hnot : 1 ∉ s.filter Nat.Prime := by
    simp [s, one_not_natPrime]
  rw [Finset.card_insert_of_notMem hnot]

/-- Neutral parameters naming the analytic/computability material discussed in
Misra's paper.  These are data types, not propositions. -/
structure MisraAnalyticParameters where
  pntEntropyApproximationModel : Type
  vonKochRHErrorEquivalenceModel : Type
  entropyRHImplicationModel : Type
  entropyPneqNPImplicationModel : Type
  entropyTwinPrimesImplicationModel : Type
  entropySymmetryBreakingModel : Type

end MisraPrimeEntropyDigest

end noncomputable section
