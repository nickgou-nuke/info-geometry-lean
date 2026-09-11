/-
The primitive three-direction axial channel.

This file deliberately defines the parity-twisted Levi--Civita cross channel
before any quaternionic representation theorem.  The free index is explicit;
the quaternionic commutator is a later readout, not the definition.
-/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita

open scoped BigOperators

variable {R : Type*} [CommRing R]

def leviCivita3 (k i j : Fin 3) : ℤ :=
  if k = i ∨ k = j ∨ i = j then 0
  else if
      (k, i, j) = (0, 1, 2) ∨
      (k, i, j) = (1, 2, 0) ∨
      (k, i, j) = (2, 0, 1) then 1
    else -1

def parityTwistedCross {R : Type*} [CommRing R]
    (χ : R) (u v : Fin 3 → R) (k : Fin 3) : R :=
  χ * ∑ i : Fin 3, ∑ j : Fin 3,
    (leviCivita3 k i j : R) * u i * v j

def parityTwist {R : Type*} [CommRing R]
    (χ : R) (u : Fin 3 → R) : Fin 3 → R := χ • u

theorem parityTwist_involutive {R : Type*} [CommRing R]
    (χ : R) (u : Fin 3 → R) (hχ : χ * χ = 1) :
    parityTwist χ (parityTwist χ u) = u := by
  funext k
  change χ * (χ * u k) = u k
  calc
    χ * (χ * u k) = (χ * χ) * u k := by ring
    _ = u k := by rw [hχ, one_mul]

@[simp] theorem parityTwistedCross_apply (χ : R) (u v : Fin 3 → R) (k : Fin 3) :
    parityTwistedCross χ u v k =
      χ * ∑ i : Fin 3, ∑ j : Fin 3,
        (leviCivita3 k i j : R) * u i * v j := rfl

theorem parityTwistedCross_add_left (χ : R) (u v w : Fin 3 → R) :
    parityTwistedCross χ (u + v) w =
      parityTwistedCross χ u w + parityTwistedCross χ v w := by
  funext k
  simp only [parityTwistedCross, Pi.add_apply, mul_add, add_mul]
  simp_rw [Finset.sum_add_distrib]
  ring

theorem parityTwistedCross_add_right (χ : R) (u v w : Fin 3 → R) :
    parityTwistedCross χ u (v + w) =
      parityTwistedCross χ u v + parityTwistedCross χ u w := by
  funext k
  simp only [parityTwistedCross, Pi.add_apply, mul_add, add_mul]
  simp_rw [Finset.sum_add_distrib]
  ring

theorem parityTwistedCross_swap (χ : R) (u v : Fin 3 → R) :
    parityTwistedCross χ v u = -parityTwistedCross χ u v := by
  funext k
  fin_cases k <;>
    simp [parityTwistedCross, leviCivita3, Fin.sum_univ_succ] <;> ring

@[simp] theorem parityTwistedCross_self (χ : R) (u : Fin 3 → R) :
    parityTwistedCross χ u u = 0 := by
  funext k
  fin_cases k <;>
    simp [parityTwistedCross, leviCivita3, Fin.sum_univ_succ] <;> ring

end InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita
