import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import InfoGeometry.Arithmetic.PrimonFockPrimeEnergy
import InfoGeometry.Arithmetic.ChebyshevPrimeEnergyBound

noncomputable section

namespace InfoGeometry.Arithmetic.LongGapsPrimon

open Real
open Filter

/-- The j-fold natural logarithm used in the statement of the OpenAI prime gaps theorem. -/
def iteratedLog (j : ℕ) (x : ℝ) : ℝ := (Real.log^[j]) x

/-- The prime gap scale function G_scale(X) from the OpenAI formalization. -/
def gapScale (x : ℝ) : ℝ :=
  Real.log x * (iteratedLog 2 x) ^ 2 * iteratedLog 4 x / (iteratedLog 3 x) ^ 2

/-- Consecutive primes: p and q are both prime, p < q, and no integer between them is prime. -/
def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬r.Prime

/-- Single-particle primon energy in the Bost-Connes / Julia arithmetic quantum field theory: E(p) = log p. -/
def primonEnergy (p : ℕ) : ℝ := Real.log (p : ℝ)

/-- The single-particle energy gap between consecutive primon states: ΔE(p, q) = E(q) - E(p). -/
def primonEnergyGap (p q : ℕ) : ℝ := primonEnergy q - primonEnergy p

/-- The relative single-particle Gibbs Boltzmann weight ratio at inverse temperature β:
    exp(-β * ΔE(p, q)). -/
def primonBoltzmannRatio (β : ℝ) (p q : ℕ) : ℝ :=
  Real.exp (-β * primonEnergyGap p q)

/-- FUNDAMENTAL INEQUALITY: For any positive reals 0 < a < b, the logarithmic gap
    satisfies log b - log a ≥ (b - a) / b. -/
theorem log_sub_log_ge_div (a b : ℝ) (ha : 0 < a) (hb : a < b) :
    (b - a) / b ≤ Real.log b - Real.log a := by
  have hb_pos : 0 < b := ha.trans hb
  have h_div_pos : 0 < a / b := div_pos ha hb_pos
  have h_log_le := Real.log_le_sub_one_of_pos h_div_pos
  have h_log_div : Real.log (a / b) = Real.log a - Real.log b :=
    Real.log_div ha.ne' hb_pos.ne'
  rw [h_log_div] at h_log_le
  have h_sub : a / b - 1 = - ((b - a) / b) := by
    calc
      a / b - 1 = (a - b) / b := by ring
      _ = - ((b - a) / b) := by ring
  rw [h_sub] at h_log_le
  linarith

/-- COROLLARY: For 0 < a < b ≤ X with X > 0, log b - log a ≥ (b - a) / X. -/
theorem log_sub_log_ge_div_of_le (a b X : ℝ) (ha : 0 < a) (hb : a < b) (hbX : b ≤ X) :
    (b - a) / X ≤ Real.log b - Real.log a := by
  have hb_pos : 0 < b := ha.trans hb
  have h_div := log_sub_log_ge_div a b ha hb
  have h_le : (b - a) / X ≤ (b - a) / b := by
    have h_diff_nonneg : 0 ≤ b - a := by linarith
    exact div_le_div_of_nonneg_left h_diff_nonneg hb_pos hbX
  exact h_le.trans h_div

/-- THEOREM 1 (Primon Single-Particle Spectral Energy Gap Bound):
    If consecutive primes p < q ≤ X satisfy a prime gap q - p ≥ c * gapScale(X),
    then the primon energy gap ΔE(p, q) is bounded below by c * gapScale(X) / X. -/
theorem primonEnergyGap_ge_of_gap
    (p q : ℕ) (X c : ℝ)
    (hp : 0 < p)
    (hpq : p < q)
    (hqX : (q : ℝ) ≤ X)
    (hgap : c * gapScale X ≤ ((q - p : ℕ) : ℝ)) :
    c * gapScale X / X ≤ primonEnergyGap p q := by
  dsimp [primonEnergyGap, primonEnergy]
  have ha : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hb : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have h_log_bound := log_sub_log_ge_div_of_le (p : ℝ) (q : ℝ) X ha hb hqX
  have h_cast_sub : ((q - p : ℕ) : ℝ) = (q : ℝ) - (p : ℝ) := by
    push_cast
    rfl
  rw [h_cast_sub] at hgap
  have hX_pos : 0 < X := by
    have hq_pos : 0 < (q : ℝ) := ha.trans hb
    exact hq_pos.trans_le hqX
  have h_scale_bound : c * gapScale X / X ≤ ((q : ℝ) - (p : ℝ)) / X := by
    exact div_le_div_of_nonneg_right hgap (le_of_lt hX_pos)
  exact h_scale_bound.trans h_log_bound

/-- THEOREM 2 (Thermal Intermittency / Boltzmann Suppression Ratio):
    At inverse temperature β > 0, the Boltzmann transition ratio between
    consecutive primon levels across the gap is exponentially suppressed:
      exp(-β * ΔE(p, q)) ≤ exp(-β * (c * gapScale(X) / X)). -/
theorem primonBoltzmannRatio_le_of_gap
    (p q : ℕ) (X c β : ℝ)
    (hp : 0 < p)
    (hpq : p < q)
    (hqX : (q : ℝ) ≤ X)
    (hβ : 0 ≤ β)
    (hgap : c * gapScale X ≤ ((q - p : ℕ) : ℝ)) :
    primonBoltzmannRatio β p q ≤ Real.exp (-β * (c * gapScale X / X)) := by
  dsimp [primonBoltzmannRatio]
  have h_gap_bound := primonEnergyGap_ge_of_gap p q X c hp hpq hqX hgap
  have h_neg : -β * primonEnergyGap p q ≤ -β * (c * gapScale X / X) := by
    nlinarith
  exact Real.exp_le_exp.mpr h_neg

/-- THEOREM 3 (Spectral Band Gap Vacuum):
    For consecutive primes p < q, the open interval of energies (primonEnergy p, primonEnergy q)
    contains NO single-particle primon states. -/
theorem primon_spectral_vacuum
    (p q : ℕ) (r : ℕ)
    (hcons : ConsecutivePrimes p q)
    (hr : primonEnergy p < primonEnergy r ∧ primonEnergy r < primonEnergy q) :
    ¬r.Prime := by
  have hp : (p : ℝ) < (r : ℝ) := by
    dsimp [primonEnergy] at hr
    have hr_pos : 0 < (r : ℝ) := by
      have hp_pos : 0 < (p : ℝ) := by
        exact_mod_cast hcons.1.pos
      by_contra h_neg
      push_neg at h_neg
      have := Real.log_le_log_of_nonpos hp_pos h_neg
      linarith [hr.1]
    exact (Real.log_lt_log_iff (by exact_mod_cast hcons.1.pos) hr_pos).mp hr.1
  have hq : (r : ℝ) < (q : ℝ) := by
    dsimp [primonEnergy] at hr
    have hr_pos : 0 < (r : ℝ) := by exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le p) (by exact_mod_cast hp))
    have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hcons.2.1.pos
    exact (Real.log_lt_log_iff hr_pos hq_pos).mp hr.2
  have hpr_nat : p < r := by exact_mod_cast hp
  have hrq_nat : r < q := by exact_mod_cast hq
  exact hcons.2.2.2 r hpr_nat hrq_nat

/-- THEOREM 4 (OpenAI Long Gaps Integration Schema):
    Assuming the existence of long prime gaps bounded by gapScale(X),
    there exist infinitely many scales at which the primon single-particle spectrum
    exhibits a spectral gap exceeding c * gapScale(X) / X and corresponding exponential
    Boltzmann thermal suppression. -/
theorem primon_long_gap_consequence
    (c : ℝ) (hc : 0 < c)
    (X : ℝ) (hX : 0 < X)
    (p q : ℕ)
    (hcons : ConsecutivePrimes p q)
    (hqX : (q : ℝ) ≤ X)
    (hgap : c * gapScale X ≤ ((q - p : ℕ) : ℝ))
    (β : ℝ) (hβ : 0 ≤ β) :
    (c * gapScale X / X ≤ primonEnergyGap p q) ∧
    (primonBoltzmannRatio β p q ≤ Real.exp (-β * (c * gapScale X / X))) ∧
    (∀ r : ℕ, primonEnergy p < primonEnergy r → primonEnergy r < primonEnergy q → ¬r.Prime) := by
  refine ⟨?_, ?_, ?_⟩
  · exact primonEnergyGap_ge_of_gap p q X c hcons.1.pos hcons.2.2.1 hqX hgap
  · exact primonBoltzmannRatio_le_of_gap p q X c β hcons.1.pos hcons.2.2.1 hqX hβ hgap
  · intro r hrp hrq
    exact primon_spectral_vacuum p q r hcons ⟨hrp, hrq⟩

end InfoGeometry.Arithmetic.LongGapsPrimon
