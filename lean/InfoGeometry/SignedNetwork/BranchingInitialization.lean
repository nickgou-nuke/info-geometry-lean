import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.SignedNetwork.ExactCancellation

/-! Finite signed initialization.

The signed network stores integer counts, while a finite real coordinate vector
is represented in expectation by sampling a label with weight proportional to
its absolute value and retaining its sign.  This owner deliberately stops at
the finite weighted identity; it does not identify an ensemble with a single
real-valued count.
-/

namespace InfoGeometry.SignedNetwork.BranchingInitialization

open InfoGeometry.SignedNetwork.ExactCancellation

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C]

def seedMass (w : C → ℝ) : ℝ := ∑ a, |w a|

def seedSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem abs_mul_seedSign (x : ℝ) : |x| * seedSign x = x := by
  by_cases hx : 0 ≤ x
  · simp [seedSign, hx, abs_of_nonneg hx]
  · simp [seedSign, hx, abs_of_neg (lt_of_not_ge hx)]

theorem seedMass_nonneg (w : C → ℝ) : 0 ≤ seedMass w := by
  exact Finset.sum_nonneg fun a _ => abs_nonneg (w a)

def seedProbability (w : C → ℝ) (a : C) : ℝ :=
  if seedMass w = 0 then 0 else |w a| / seedMass w

theorem seedProbability_nonneg (w : C → ℝ) (a : C) :
    0 ≤ seedProbability w a := by
  unfold seedProbability
  split_ifs
  · exact le_rfl
  · exact div_nonneg (abs_nonneg _) (seedMass_nonneg w)

theorem seedMass_zero_coordinate (w : C → ℝ) (h : seedMass w = 0) (a : C) :
    w a = 0 := by
  have ha : |w a| ≤ seedMass w := by
    exact Finset.single_le_sum (fun b _ => abs_nonneg (w b)) (Finset.mem_univ a)
  rw [h] at ha
  exact abs_eq_zero.mp (le_antisymm ha (abs_nonneg _))

def seed (w : C → ℝ) (a : C) : Counts C :=
  if 0 ≤ w a then ⟨fun x => if x = a then 1 else 0, fun _ => 0⟩
  else ⟨fun _ => 0, fun x => if x = a then 1 else 0⟩

theorem seed_signed (w : C → ℝ) (a x : C) :
    ((seed w a).positive x : ℝ) - (seed w a).negative x =
      if x = a then seedSign (w a) else 0 := by
  by_cases ha : 0 ≤ w a <;> by_cases hx : x = a <;>
    simp [seed, seedSign, ha, hx]

theorem weighted_seed_readout (w : C → ℝ) (h : seedMass w ≠ 0) (a x : C) :
    seedProbability w a * (seedMass w *
      (((seed w a).positive x : ℝ) - (seed w a).negative x)) =
      if x = a then w a else 0 := by
  rw [seed_signed]
  by_cases hx : x = a
  · simp only [hx, if_true]
    unfold seedProbability
    rw [if_neg h]
    field_simp [h]
    exact abs_mul_seedSign (w a)
  · simp [hx]

theorem weighted_seed_sum (w : C → ℝ) (x : C) :
    (∑ a, seedProbability w a * (seedMass w *
      (((seed w a).positive x : ℝ) - (seed w a).negative x))) = w x := by
  by_cases h : seedMass w = 0
  · have hx := seedMass_zero_coordinate w h x
    rw [hx]
    simp [seedProbability, h]
  · simp_rw [weighted_seed_readout w h]
    simp

end
end InfoGeometry.SignedNetwork.BranchingInitialization
