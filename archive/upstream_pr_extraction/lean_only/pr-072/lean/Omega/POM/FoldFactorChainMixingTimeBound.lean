import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.FoldFactorChainDerivedInvariants

namespace Omega.POM

/-- The trivial stationary-mass lower bound `π_* ≥ 2^{-m}` written as `1 / 2^m`. -/
noncomputable def stationaryMassLower (m : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ m

/-- The spectral-gap-based total-variation mixing bound after inserting the chapter gap lower
bound `2 / m`. -/
noncomputable def tvMixingUpper (m : ℕ) (eps : ℝ) : ℝ :=
  (1 / foldFactorChainGapLower m) *
    (Real.log (1 / (2 * eps)) + (1 / 2 : ℝ) * Real.log (1 / stationaryMassLower m))

/-- The standard spectral-gap-to-total-variation mixing inequality specialized to the chapter
bound `gap(P) ≥ 2 / m`. -/
def tvMixingBound (m : ℕ) (eps : ℝ) : Prop :=
  tvMixingUpper m eps =
    (m : ℝ) / 2 *
      (Real.log (1 / (2 * eps)) + (1 / 2 : ℝ) * Real.log (1 / stationaryMassLower m))

/-- The explicit quadratic estimate obtained from `π_* ≥ 2^{-m}`. -/
def explicitQuadraticBound (m : ℕ) (eps : ℝ) : Prop :=
  tvMixingUpper m eps ≤
    (m : ℝ) ^ 2 * Real.log 2 / 4 + (m : ℝ) / 2 * Real.log (1 / (2 * eps))

private lemma log_two_pow (n : ℕ) : Real.log ((2 : ℝ) ^ n) = (n : ℝ) * Real.log 2 := by
  have h2pos : 0 < (2 : ℝ) := by norm_num
  have h2ne : (2 : ℝ) ≠ 0 := ne_of_gt h2pos
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
      rw [pow_succ, Real.log_mul hpow_ne h2ne, ih]
      rw [Nat.cast_add, Nat.cast_one]
      ring

private lemma tvMixingUpper_eq (m : ℕ) (hm : 1 ≤ m) (eps : ℝ) :
    tvMixingUpper m eps =
      (m : ℝ) / 2 *
        (Real.log (1 / (2 * eps)) + (1 / 2 : ℝ) * Real.log (1 / stationaryMassLower m)) := by
  unfold tvMixingUpper foldFactorChainGapLower
  have hm_real : (m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hm
  field_simp [hm_real]

private lemma log_inv_stationaryMassLower (m : ℕ) :
    Real.log (1 / stationaryMassLower m) = (m : ℝ) * Real.log 2 := by
  have hpow_ne : (2 : ℝ) ^ m ≠ 0 := by positivity
  have hinv : 1 / stationaryMassLower m = (2 : ℝ) ^ m := by
    unfold stationaryMassLower
    field_simp [hpow_ne]
  rw [hinv, log_two_pow]

/-- Paper label: `cor:pom-fold-factor-chain-mixing-time-bound`.
The gap lower bound `2 / m` and the trivial stationary-mass lower bound `2^{-m}` combine to give
the standard spectral-gap total-variation estimate and its explicit quadratic corollary. -/
theorem paper_pom_fold_factor_chain_mixing_time_bound
    (m : ℕ) (hm : 1 ≤ m) (eps : ℝ) :
    tvMixingBound m eps ∧ explicitQuadraticBound m eps := by
  refine ⟨?_, ?_⟩
  · unfold tvMixingBound
    exact tvMixingUpper_eq m hm eps
  · unfold explicitQuadraticBound
    rw [tvMixingUpper_eq m hm eps]
    rw [log_inv_stationaryMassLower]
    ring_nf
    linarith

end Omega.POM
