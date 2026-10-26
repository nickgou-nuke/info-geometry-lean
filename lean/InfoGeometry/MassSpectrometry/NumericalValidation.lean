/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.MassSpectrometry.RationalCandidate

/-!
# Numerical residuals with explicit tolerances

All computations use rational input. Bounds concern these exact values;
conversion from a GPU buffer needs its own error bound. Approximate matrix
balance is kept distinct from exact Birkhoff membership.
-/

namespace InfoGeometry.MassSpectrometry
namespace NumericalValidation

/-- Nonnegative entries and bounded row/column residuals. -/
def AssignmentWithin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (ε : ℚ) : Prop :=
  0 ≤ ε ∧ (∀ i j, (0 : ℚ) ≤ A i j) ∧
  (∀ i, |(∑ j, A i j) - 1| ≤ ε) ∧
  (∀ j, |(∑ i, A i j) - 1| ≤ ε)

instance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (ε : ℚ) :
    Decidable (AssignmentWithin A ε) := by
  letI : ∀ i j, Decidable ((0 : ℚ) ≤ A i j) := fun i j => Rat.instDecidableLe _ _
  unfold AssignmentWithin
  infer_instance

def checkAssignment {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (ε : ℚ) : Bool :=
  decide (AssignmentWithin A ε)

@[simp] theorem checkAssignment_eq_true_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (ε : ℚ) :
    checkAssignment A ε = true ↔ AssignmentWithin A ε := by simp [checkAssignment]

/-- A zero residual check gives exact membership; a positive tolerance does not. -/
theorem checkAssignment_zero_sound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (h : checkAssignment A 0 = true) :
    IsSoftAssignment (fun i j => (A i j : ℝ)) := by
  have hA := (checkAssignment_eq_true_iff A 0).mp h
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact_mod_cast hA.2.1 i j
  · intro i
    have hi := hA.2.2.1 i
    have hi' : (∑ j, A i j) = 1 := by simpa [sub_eq_zero] using hi
    exact_mod_cast hi'
  · intro j
    have hj := hA.2.2.2 j
    have hj' : (∑ i, A i j) = 1 := by simpa [sub_eq_zero] using hj
    exact_mod_cast hj'

/-- The exact real-valued meaning of a checked row residual. -/
theorem checkAssignment_row_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (ε : ℚ) (h : checkAssignment A ε = true) (i : Fin n) :
    |(∑ j, (A i j : ℝ)) - 1| ≤ (ε : ℝ) := by
  exact_mod_cast ((checkAssignment_eq_true_iff A ε).mp h).2.2.1 i

/-- Check every nonzero proposed assignment against an absolute mass tolerance.
Both arrays must be in the same mass/charge convention before this check. -/
def checkMassFit {n k : ℕ} (c : RationalCandidate n k) (ε : ℚ) : Bool := by
  letI : ∀ i j, Decidable (c.assignment i j = (0 : ℚ)) :=
    fun i j => (inferInstance : DecidableEq ℚ) (c.assignment i j) 0
  exact decide (0 ≤ ε ∧ ∀ i j, c.assignment i j ≠ (0 : ℚ) →
    |c.peakMass i - c.fragmentMass j| ≤ ε)

theorem checkMassFit_sound {n k : ℕ} (c : RationalCandidate n k) (ε : ℚ)
    (h : checkMassFit c ε = true) {i j : Fin n} (ha : c.assignment i j ≠ (0 : ℚ)) :
    |(c.peakMass i : ℝ) - (c.fragmentMass j : ℝ)| ≤ (ε : ℝ) := by
  let : ∀ i j, Decidable (c.assignment i j = (0 : ℚ)) :=
    fun i j => (inferInstance : DecidableEq ℚ) (c.assignment i j) 0
  have hh : 0 ≤ ε ∧ ∀ i j, c.assignment i j ≠ (0 : ℚ) →
      |c.peakMass i - c.fragmentMass j| ≤ ε := of_decide_eq_true h
  exact_mod_cast hh.2 i j ha

/-- Coordinatewise finite-sample residual check, suitable for supplied
simulate-after-reconstruct outputs. It asserts nothing about other inputs. -/
def checkObservedResidual {s n : ℕ}
    (observed predicted : Fin s → Fin n → ℚ) (ε : ℚ) : Bool :=
  decide (0 ≤ ε ∧ ∀ e i, |predicted e i - observed e i| ≤ ε)

theorem checkObservedResidual_sound {s n : ℕ}
    (observed predicted : Fin s → Fin n → ℚ) (ε : ℚ)
    (h : checkObservedResidual observed predicted ε = true) (e : Fin s) (i : Fin n) :
    |(predicted e i : ℝ) - (observed e i : ℝ)| ≤ (ε : ℝ) := by
  have hh : 0 ≤ ε ∧ ∀ e i, |predicted e i - observed e i| ≤ ε := of_decide_eq_true h
  exact_mod_cast hh.2 e i

end NumericalValidation
end InfoGeometry.MassSpectrometry
