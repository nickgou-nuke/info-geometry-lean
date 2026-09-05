import InfoGeometry.SignedNetwork.BranchingEventLaw

/-!
# Unbiased finite signed initialization

An arbitrary real coordinate vector need not be an integer count difference.
One seed is drawn with probability proportional to the absolute coordinate,
its sign is retained, and its common weight is the L1 mass. This realizes the
initial coordinates in expectation. A zero vector is represented by no seed.

For M independent copies, averaging their weighted readouts gives the same
initial expectation; no normalization of raw signed counts to a probability
vector is assumed.
-/

noncomputable section

namespace InfoGeometry.SignedNetwork.BranchingInitialization

open MeasureTheory
open InfoGeometry.SignedNetwork.ExactCancellation
open InfoGeometry.SignedNetwork.BranchingEnsembleGenerator

variable {C : Type*} [Fintype C] [DecidableEq C]

def seedMass (w : C → ℝ) : ℝ := ∑ a, |w a|

def seedSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem abs_mul_seedSign (x : ℝ) : |x| * seedSign x = x := by
  by_cases hx : 0 ≤ x
  · simp [seedSign, hx, abs_of_nonneg hx]
  · simp [seedSign, hx, abs_of_neg (lt_of_not_ge hx)]

theorem seedMass_nonneg (w : C → ℝ) : 0 ≤ seedMass w :=
  Finset.sum_nonneg (fun a _ => abs_nonneg (w a))

theorem coordinate_eq_zero_of_seedMass_zero (w : C → ℝ)
    (hZ : seedMass w = 0) (a : C) : w a = 0 := by
  have hle : |w a| ≤ seedMass w :=
    Finset.single_le_sum (fun b _ => abs_nonneg (w b)) (Finset.mem_univ a)
  rw [hZ] at hle
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg (w a)))

def seedProbability (w : C → ℝ) : Option C → ℝ
  | none => if seedMass w = 0 then 1 else 0
  | some a => if seedMass w = 0 then 0 else |w a| / seedMass w

theorem seedProbability_nonneg (w : C → ℝ) (a : Option C) :
    0 ≤ seedProbability w a := by
  cases a with
  | none => simp only [seedProbability]; split_ifs <;> norm_num
  | some a =>
      simp only [seedProbability]
      split_ifs
      · exact le_rfl
      · exact div_nonneg (abs_nonneg _) (seedMass_nonneg w)

theorem sum_seedProbability (w : C → ℝ) : (∑ a, seedProbability w a) = 1 := by
  classical
  by_cases hZ : seedMass w = 0
  · simp [Fintype.sum_option, seedProbability, hZ]
  · simp only [Fintype.sum_option, seedProbability, hZ, if_false, zero_add, add_zero]
    rw [← Finset.sum_div]
    exact div_self hZ

def seedPMF (w : C → ℝ) : PMF (Option C) :=
  PMF.ofFintype (fun a => ENNReal.ofReal (seedProbability w a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun a _ => seedProbability_nonneg w a), sum_seedProbability]
    simp)

@[simp] theorem seedPMF_toReal (w : C → ℝ) (a : Option C) :
    (seedPMF w a).toReal = seedProbability w a :=
  ENNReal.toReal_ofReal (seedProbability_nonneg w a)

/-- The sample is an actual positive or negative count, not a real coordinate
silently substituted for a particle. -/
def seed (w : C → ℝ) : Option C → Counts C
  | none => ⟨fun _ => 0, fun _ => 0⟩
  | some a => if 0 ≤ w a then ⟨atom a, fun _ => 0⟩ else ⟨fun _ => 0, atom a⟩

@[simp] theorem signedReal_seed_none (w : C → ℝ) (x : C) :
    signedReal (seed w none) x = 0 := by
  simp [seed]

theorem signedReal_seed_some (w : C → ℝ) (a x : C) :
    signedReal (seed w (some a)) x = if x = a then seedSign (w a) else 0 := by
  by_cases ha : 0 ≤ w a <;> by_cases hx : x = a <;>
    simp [seed, ha, atom, hx, seedSign]

/-- Each nonempty outcome contains exactly one sample. -/
theorem population_seed_some (w : C → ℝ) (a : C) :
    population (seed w (some a)) = 1 := by
  by_cases ha : 0 ≤ w a <;> simp [seed, ha, population, atom]

/-- Exact weighted contribution of one cell to the initial expectation. -/
theorem weighted_seed_term (w : C → ℝ) (hZ : seedMass w ≠ 0) (a x : C) :
    (|w a| / seedMass w) * (seedMass w * signedReal (seed w (some a)) x) =
      if x = a then w a else 0 := by
  rw [signedReal_seed_some]
  by_cases hx : x = a
  · simp only [hx, if_true]
    calc
      _ = |w a| * seedSign (w a) := by field_simp [hZ] <;> ring
      _ = w a := abs_mul_seedSign (w a)
  · simp [hx]

section Expectation

variable [MeasurableSpace C] [MeasurableSingletonClass C]

/-- Genuine unbiased initialization for every real finite coordinate vector. -/
theorem integral_weighted_seed (w : C → ℝ) (x : C) :
    (∫ a, seedMass w * signedReal (seed w a) x ∂(seedPMF w).toMeasure) = w x := by
  rw [PMF.integral_eq_sum]
  simp only [seedPMF_toReal, smul_eq_mul]
  by_cases hZ : seedMass w = 0
  · rw [coordinate_eq_zero_of_seedMass_zero w hZ x]
    simp [hZ]
  · simp only [Fintype.sum_option, seedProbability, hZ, if_false,
      zero_mul, zero_add, add_zero]
    simp_rw [weighted_seed_term w hZ]
    simp

end Expectation

end InfoGeometry.SignedNetwork.BranchingInitialization
