import Mathlib
import InfoGeometry.SignedNetwork.ExactCancellation
import InfoGeometry.SignedNetwork.BranchingEventLaw

/-! Finite ensemble transitions for the marked source-target event law. -/
namespace InfoGeometry.SignedNetwork.BranchingEnsembleGenerator

noncomputable section
open InfoGeometry.SignedNetwork.ExactCancellation
open InfoGeometry.SignedNetwork.BranchingEventLaw

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

end
end InfoGeometry.SignedNetwork.BranchingEnsembleGenerator
