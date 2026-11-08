import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.CuntzPrimeCriticalEulerFactorBridge

/-!
# Finite prime Gibbs normalization and critical local weight

This owner formalizes only finite prime-cutoff normalization.  It reuses the
critical-line amplitude/phase factorization from
`CuntzPrimeCriticalEulerFactorBridge` and does not assert a normalized
probability measure over all primes at `β = 1`.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.CuntzPrimeFiniteGibbsBridge

open scoped BigOperators
open InfoGeometry.Arithmetic.CuntzPrimeCriticalEulerFactorBridge
open InfoGeometry.Algebra.CuntzModularAutomorphism
open InfoGeometry.Algebra.CuntzModularPhaseCharacterBridge

def finitePrimeGibbsWeight (β : ℝ) (p : Nat.Primes) : ℝ :=
  ((p : ℕ) : ℝ) ^ (-β)

def finitePrimePartition (S : Finset Nat.Primes) (β : ℝ) : ℝ :=
  S.sum (fun p => finitePrimeGibbsWeight β p)

def finitePrimeGibbsProbability
    (S : Finset Nat.Primes) (β : ℝ) (p : Nat.Primes) : ℝ :=
  if p ∈ S then finitePrimeGibbsWeight β p / finitePrimePartition S β else 0

/-! ## Finite Hellinger amplitude and modular phase readout -/

/-- The positive Hellinger amplitude of a finite Gibbs probability. -/
noncomputable def finitePrimeGibbsAmplitude
    (S : Finset Nat.Primes) (β : ℝ) (p : Nat.Primes) : ℝ :=
  Real.sqrt (finitePrimeGibbsProbability S β p)

/-- Add the existing Cuntz modular phase to the finite Gibbs amplitude. -/
noncomputable def finitePrimeGibbsWave
    (S : Finset Nat.Primes) (β E : ℝ) (p : Nat.Primes) : ℂ :=
  (finitePrimeGibbsAmplitude S β p : ℂ) * modularPhase (p : ℕ) (-E)

theorem finitePrimeGibbsWeight_pos (β : ℝ) (p : Nat.Primes) :
    0 < finitePrimeGibbsWeight β p := by
  unfold finitePrimeGibbsWeight
  apply Real.rpow_pos_of_pos
  exact_mod_cast p.property.pos

theorem finitePrimePartition_pos
    (S : Finset Nat.Primes) (β : ℝ) (hS : S.Nonempty) :
    0 < finitePrimePartition S β := by
  unfold finitePrimePartition
  apply Finset.sum_pos'
  · intro p hp
    exact (finitePrimeGibbsWeight_pos β p).le
  · rcases hS with ⟨p, hp⟩
    exact ⟨p, hp, finitePrimeGibbsWeight_pos β p⟩

theorem finitePrimeGibbsProbability_nonneg
    (S : Finset Nat.Primes) (β : ℝ) (hS : S.Nonempty)
    (p : Nat.Primes) :
    0 ≤ finitePrimeGibbsProbability S β p := by
  unfold finitePrimeGibbsProbability
  split_ifs
  · exact div_nonneg (finitePrimeGibbsWeight_pos β p).le
      (finitePrimePartition_pos S β hS).le
  · exact le_rfl

theorem finitePrimeGibbsProbability_pos_of_mem
    (S : Finset Nat.Primes) (β : ℝ) (hS : S.Nonempty)
    {p : Nat.Primes} (hp : p ∈ S) :
    0 < finitePrimeGibbsProbability S β p := by
  simp only [finitePrimeGibbsProbability, if_pos hp]
  exact div_pos (finitePrimeGibbsWeight_pos β p)
    (finitePrimePartition_pos S β hS)

theorem finitePrimeGibbsProbability_sum
    (S : Finset Nat.Primes) (β : ℝ) (hS : S.Nonempty) :
    S.sum (fun p => finitePrimeGibbsProbability S β p) = 1 := by
  have hpart : finitePrimePartition S β ≠ 0 :=
    (finitePrimePartition_pos S β hS).ne'
  calc
    S.sum (fun p => finitePrimeGibbsProbability S β p) =
        S.sum (fun p => finitePrimeGibbsWeight β p /
          finitePrimePartition S β) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [finitePrimeGibbsProbability, hp, div_eq_mul_inv]
    _ = (finitePrimePartition S β) / finitePrimePartition S β := by
      rw [← Finset.sum_div]
      rfl
    _ = 1 := div_self hpart

theorem finitePrimeGibbsAmplitude_sq
    (S : Finset Nat.Primes) (β : ℝ) (hS : S.Nonempty)
    (p : Nat.Primes) :
    finitePrimeGibbsAmplitude S β p ^ 2 =
      finitePrimeGibbsProbability S β p := by
  unfold finitePrimeGibbsAmplitude
  rw [Real.sq_sqrt]
  exact finitePrimeGibbsProbability_nonneg S β hS p

theorem finitePrimeGibbsAmplitude_pos_of_mem
    (S : Finset Nat.Primes) (β : ℝ) (hS : S.Nonempty)
    {p : Nat.Primes} (hp : p ∈ S) :
    0 < finitePrimeGibbsAmplitude S β p := by
  unfold finitePrimeGibbsAmplitude
  exact Real.sqrt_pos.2 (finitePrimeGibbsProbability_pos_of_mem S β hS hp)

theorem finitePrimeGibbsAmplitude_sq_sum
    (S : Finset Nat.Primes) (β : ℝ) (hS : S.Nonempty) :
    S.sum (fun p => finitePrimeGibbsAmplitude S β p ^ 2) = 1 := by
  calc
    S.sum (fun p => finitePrimeGibbsAmplitude S β p ^ 2) =
        S.sum (fun p => finitePrimeGibbsProbability S β p) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact finitePrimeGibbsAmplitude_sq S β hS p
    _ = 1 := finitePrimeGibbsProbability_sum S β hS

theorem finitePrimeGibbsWave_normSq
    (S : Finset Nat.Primes) (β E : ℝ) (hS : S.Nonempty)
    (p : Nat.Primes) :
    Complex.normSq (finitePrimeGibbsWave S β E p) =
      finitePrimeGibbsProbability S β p := by
  unfold finitePrimeGibbsWave
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  rw [modularPhase_normSq_eq_one]
  simp only [mul_one]
  simpa [pow_two] using finitePrimeGibbsAmplitude_sq S β hS p

theorem finitePrimeGibbsWave_normSq_sum
    (S : Finset Nat.Primes) (β E : ℝ) (hS : S.Nonempty) :
    S.sum (fun p => Complex.normSq (finitePrimeGibbsWave S β E p)) = 1 := by
  calc
    S.sum (fun p => Complex.normSq (finitePrimeGibbsWave S β E p)) =
        S.sum (fun p => finitePrimeGibbsProbability S β p) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact finitePrimeGibbsWave_normSq S β E hS p
    _ = 1 := finitePrimeGibbsProbability_sum S β hS

theorem finitePrimeGibbsWeight_one (p : Nat.Primes) :
    finitePrimeGibbsWeight 1 p = 1 / ((p : ℕ) : ℝ) := by
  unfold finitePrimeGibbsWeight
  rw [Real.rpow_neg_one]
  simp [one_div]

theorem primeCriticalLineWeight_amplitude_phase_readout
    (p : ℕ) (E : ℝ) :
    primeCriticalLineWeight p E =
      (Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) : ℂ) *
        modularPhase p (-E) := by
  exact primeCriticalLineWeight_amplitude_phase p E

theorem primeCriticalLineWeight_normSq
    (p : ℕ) (E : ℝ) :
    Complex.normSq (primeCriticalLineWeight p E) =
      Real.exp (-Real.log (p : ℝ)) := by
  rw [primeCriticalLineWeight_amplitude_phase_readout]
  rw [Complex.normSq_mul, Complex.normSq_ofReal,
    modularPhase_normSq_eq_one]
  simp only [mul_one]
  rw [← Real.exp_add]
  congr 1
  ring

theorem primeCriticalLineWeight_normSq_eq_gibbsWeight_one
    (p : Nat.Primes) (E : ℝ) :
    Complex.normSq (primeCriticalLineWeight (p : ℕ) E) =
      finitePrimeGibbsWeight 1 p := by
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.property.pos
  rw [primeCriticalLineWeight_normSq, finitePrimeGibbsWeight_one]
  rw [Real.exp_neg, Real.exp_log hp]
  simp [one_div]

end InfoGeometry.Arithmetic.CuntzPrimeFiniteGibbsBridge
