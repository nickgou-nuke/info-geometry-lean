import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open scoped BigOperators

namespace InfoGeometry.SuperTwistor

variable {R : Type*} [CommRing R]

def bosonicScaleFactor (t : R) (n : ℕ) : R := t ^ n
def fermionicBerezinScaleFactor (t : Rˣ) (m : ℕ) : R := ((t⁻¹ : Rˣ) : R) ^ m
def superBerezinianScaleFactor (t : Rˣ) (n m : ℕ) : R :=
  bosonicScaleFactor (t : R) n * fermionicBerezinScaleFactor t m

theorem super_twistor_measure_projective_invariance (t : Rˣ) :
    superBerezinianScaleFactor t 4 4 = 1 := by
  dsimp [superBerezinianScaleFactor, bosonicScaleFactor, fermionicBerezinScaleFactor]
  rw [← mul_pow]
  have h_inv : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  rw [h_inv, one_pow]

abbrev Superfield (R : Type*) := (Fin 4 → Bool) → R
def topMonomial : Fin 4 → Bool := fun _ => true
def berezinIntegral (F : Superfield R) : R := F topMonomial

def signCount (s : Fin 4 → Bool) (i : Fin 4) : ℕ :=
  (Finset.univ.filter (fun j : Fin 4 => j < i ∧ s j = true)).card

def fermSign (s : Fin 4 → Bool) (i : Fin 4) : R :=
  if (signCount s i) % 2 = 1 then -1 else 1

def updateCoord (s : Fin 4 → Bool) (i : Fin 4) (b : Bool) : Fin 4 → Bool :=
  fun j => if j = i then b else s j

lemma updateCoord_self (s : Fin 4 → Bool) (i : Fin 4) (b : Bool) :
    updateCoord s i b i = b := by
  dsimp [updateCoord]
  rw [if_pos rfl]

def fermDeriv (i : Fin 4) (F : Superfield R) : Superfield R :=
  fun s => if s i = false then fermSign s i * F (updateCoord s i true) else 0

theorem fermDeriv_sq_zero (i : Fin 4) (F : Superfield R) :
    fermDeriv i (fermDeriv i F) = 0 := by
  ext s
  change (if s i = false then fermSign s i * (fermDeriv i F (updateCoord s i true)) else 0) = 0
  by_cases h1 : s i = false
  · rw [if_pos h1]
    change fermSign s i * (if updateCoord s i true i = false then _ else 0) = 0
    have h2 : updateCoord s i true i = true := updateCoord_self s i true
    have h3 : ¬(updateCoord s i true i = false) := by
      intro h
      rw [h2] at h
      exact Bool.noConfusion h
    rw [if_neg h3, mul_zero]
  · rw [if_neg h1]

theorem berezinIntegral_fermDeriv (i : Fin 4) (F : Superfield R) :
    berezinIntegral (fermDeriv i F) = 0 := by
  rfl

def supercharge (ε : Fin 4 → R) (F : Superfield R) : Superfield R :=
  fun s => ∑ i : Fin 4, ε i * fermDeriv i F s

theorem supercharge_invariance (ε : Fin 4 → R) (F : Superfield R) :
    berezinIntegral (supercharge ε F) = 0 := by
  dsimp [berezinIntegral, supercharge]
  have h_zero : ∀ i : Fin 4, fermDeriv i F topMonomial = 0 := by
    intro i
    rfl
  have h_term : ∀ i : Fin 4, ε i * fermDeriv i F topMonomial = 0 := by
    intro i
    rw [h_zero i, mul_zero]
  simp only [h_term, Finset.sum_const_zero]

def chiralTwistorSupercharge (z : Fin 4 → R) (a : Fin 4) (A : Fin 4) (F : Superfield R) : Superfield R :=
  fun s => z a * fermDeriv A F s

theorem chiral_twistor_supercharge_invariance
    (z : Fin 4 → R) (a : Fin 4) (A : Fin 4) (F : Superfield R) :
    berezinIntegral (chiralTwistorSupercharge z a A F) = 0 := by
  dsimp [berezinIntegral, chiralTwistorSupercharge]
  have h_zero : fermDeriv A F topMonomial = 0 := by
    rfl
  rw [h_zero, mul_zero]

theorem chiralTwistorSupercharge_sq_zero
    (z : Fin 4 → R) (a : Fin 4) (A : Fin 4) (F : Superfield R) :
    chiralTwistorSupercharge z a A (chiralTwistorSupercharge z a A F) = 0 := by
  ext s
  change z a * fermDeriv A (chiralTwistorSupercharge z a A F) s = 0
  change z a * (if s A = false then fermSign s A * chiralTwistorSupercharge z a A F (updateCoord s A true) else 0) = 0
  by_cases h1 : s A = false
  · rw [if_pos h1]
    change z a * (fermSign s A * (z a * fermDeriv A F (updateCoord s A true))) = 0
    change z a * (fermSign s A * (z a * (if updateCoord s A true A = false then _ else 0))) = 0
    have h2 : updateCoord s A true A = true := updateCoord_self s A true
    have h3 : ¬(updateCoord s A true A = false) := by
      intro h
      rw [h2] at h
      exact Bool.noConfusion h
    rw [if_neg h3, mul_zero, mul_zero, mul_zero]
  · rw [if_neg h1, mul_zero]

end InfoGeometry.SuperTwistor
