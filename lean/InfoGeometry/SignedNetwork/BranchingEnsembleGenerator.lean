/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.SignedNetwork.ExactCancellation
import InfoGeometry.SignedNetwork.BranchingEventLaw
import InfoGeometry.SignedNetwork.BalancedPairKernel

/-! Finite ensemble transitions for the marked source-target event law. -/
namespace InfoGeometry.SignedNetwork.BranchingEnsembleGenerator

noncomputable section
open InfoGeometry.SignedNetwork.ExactCancellation
open InfoGeometry.SignedNetwork.BranchingEventLaw
open InfoGeometry.SignedNetwork.BalancedPairKernel

variable {C : Type*} [Fintype C] [DecidableEq C]

def atom (a x : C) : ℕ := if x = a then 1 else 0

def birthPositive (p : Counts C) (source target : C) : Counts C :=
  { positive := fun x => p.positive x + atom target x
    negative := fun x => p.negative x + atom source x }

def signedReal (p : Counts C) (x : C) : ℝ :=
  (signed p x : ℝ)

def population (p : Counts C) : ℕ :=
  ∑ x, (p.positive x + p.negative x)

@[simp] theorem signedReal_eq (p : Counts C) (x : C) :
    signedReal p x = (p.positive x : ℝ) - (p.negative x : ℝ) := by
  simp [signedReal, signed]

@[simp] theorem population_birthPositive (p : Counts C) (source target : C) :
    population (birthPositive p source target) = population p + 2 := by
  have h_atom (a : C) : (∑ x, atom a x) = 1 := by
    simp [atom]
  simp only [population, birthPositive, Finset.sum_add_distrib]
  rw [h_atom target, h_atom source]
  omega

theorem signedReal_birthPositive_sub (p : Counts C) (source target x : C) :
    signedReal (birthPositive p source target) x - signedReal p x =
      (atom target x : ℝ) - atom source x := by
  simp [signedReal_eq, birthPositive, Nat.cast_add, atom]
  ring

def applyEvent (p : Counts C) (e : Event C) : Counts C :=
  birthPositive p e.1 e.2

theorem applyEvent_signed (p : Counts C) (e : Event C) (x : C) :
    signedReal (applyEvent p e) x - signedReal p x =
      (if x = e.2 then 1 else 0) - (if x = e.1 then 1 else 0) := by
  simpa [applyEvent, atom] using signedReal_birthPositive_sub p e.1 e.2 x

theorem population_applyEvent (p : Counts C) (e : Event C) :
    population (applyEvent p e) = population p + 2 := by
  simp [applyEvent]


/-- The zero-rate case is included in the total pair intensity. -/
theorem total_pairRate_all (w : C → ℝ) (hw : ∑ a, w a = 0) :
    (∑ a, ∑ b, pairRate w a b) = positiveMass w := by
  by_cases hγ : positiveMass w = 0
  · have hw0 := zero_column_of_zero_mass w hw hγ
    simp [pairRate, positivePart, negativePart, positiveMass, hw0]
  · exact total_pairRate w hw hγ

@[simp] theorem atom_cast (a x : C) : (atom a x : ℝ) = if x = a then 1 else 0 := by
  by_cases hx : x = a <;> simp [atom, hx]

/-- A negative parent reverses both child signs. -/
def birthNegative (p : Counts C) (a b : C) : Counts C := birthPositive p a b

@[simp] theorem signedReal_cancel (p : Counts C) (x : C) :
    signedReal (cancel p) x = signedReal p x := by
  simp only [signedReal, signed_cancel]

@[simp] theorem signedReal_addNullPairs (p : Counts C) (k : C → ℕ) (x : C) :
    signedReal (addNullPairs p k) x = signedReal p x := by
  simp only [signedReal, signed_addNullPairs]

theorem signedReal_birthNegative_sub (p : Counts C) (a b x : C) :
    signedReal (birthNegative p a b) x - signedReal p x =
      -((atom a x : ℝ) - (atom b x : ℝ)) := by
  rw [birthNegative, signedReal_birthPositive_sub]
  ring

@[simp] theorem population_birthNegative (p : Counts C) (a b : C) :
    population (birthNegative p a b) = population p + 2 := by
  exact population_birthPositive p a b

theorem population_cancel_le (p : Counts C) : population (cancel p) ≤ population p := by
  apply Finset.sum_le_sum
  intro x _hx
  dsimp [cancel]
  omega

def mass (p : Counts C) : ℝ := (population p : ℝ)

theorem mass_nonneg (p : Counts C) : 0 ≤ mass p := Nat.cast_nonneg _

theorem mass_eq_sum (p : Counts C) :
    mass p = ∑ x, ((p.positive x : ℝ) + (p.negative x : ℝ)) := by
  simp [mass, population, Nat.cast_sum, Nat.cast_add]

end
end InfoGeometry.SignedNetwork.BranchingEnsembleGenerator
