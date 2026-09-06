import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.SplitOctonionChiralFockSpectrum

/-!
# Polarized Cayley triplet carrier

This file is a coefficient-frame model, not a Zorn-matrix realization.  The
two triplet slots are ordinary `Fin 3 → R` vectors, and the product records
the polarized Cayley channels:

* same-sheet vector data use the three-dimensional cross product;
* opposite-sheet vector data use the scalar dot product.

No scattering, BdG, or physical Andreev interpretation is asserted here.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonionChiralTriplet

open scoped BigOperators

variable {R : Type*} [CommRing R]

abbrev Vec3 (R : Type*) := Fin 3 → R

def dot (a b : Vec3 R) : R :=
  ∑ i : Fin 3, a i * b i

def cross (a b : Vec3 R) : Vec3 R := fun i =>
  match i with
  | 0 => a 1 * b 2 - a 2 * b 1
  | 1 => a 2 * b 0 - a 0 * b 2
  | 2 => a 0 * b 1 - a 1 * b 0

structure ChiralAmplitude (R : Type*) where
  polePlus : R
  poleMinus : R
  vectorPlus : Vec3 R
  vectorMinus : Vec3 R

namespace ChiralAmplitude

def star (x y : ChiralAmplitude R) : ChiralAmplitude R :=
  { polePlus := x.polePlus * y.polePlus - dot x.vectorPlus y.vectorMinus
    poleMinus := x.poleMinus * y.poleMinus - dot x.vectorMinus y.vectorPlus
    vectorPlus :=
      x.polePlus • y.vectorPlus + y.poleMinus • x.vectorPlus +
        cross x.vectorMinus y.vectorMinus
    vectorMinus :=
      y.polePlus • x.vectorMinus + x.poleMinus • y.vectorMinus +
        cross x.vectorPlus y.vectorPlus }

def plusTriplet (a : Vec3 R) : ChiralAmplitude R :=
  { polePlus := 0, poleMinus := 0, vectorPlus := a, vectorMinus := 0 }

def minusTriplet (a : Vec3 R) : ChiralAmplitude R :=
  { polePlus := 0, poleMinus := 0, vectorPlus := 0, vectorMinus := a }

def plusPole (r : R) : ChiralAmplitude R :=
  { polePlus := r, poleMinus := 0, vectorPlus := 0, vectorMinus := 0 }

def minusPole (r : R) : ChiralAmplitude R :=
  { polePlus := 0, poleMinus := r, vectorPlus := 0, vectorMinus := 0 }

@[simp] theorem dot_zero_left (b : Vec3 R) : dot 0 b = 0 := by
  simp [dot]

@[simp] theorem dot_zero_right (a : Vec3 R) : dot a 0 = 0 := by
  simp [dot]

@[simp] theorem cross_zero_left (b : Vec3 R) : cross 0 b = 0 := by
  funext i
  fin_cases i <;> simp [cross]

@[simp] theorem cross_zero_right (a : Vec3 R) : cross a 0 = 0 := by
  funext i
  fin_cases i <;> simp [cross]

theorem eq_iff {x y : ChiralAmplitude R} :
    x = y ↔
      x.polePlus = y.polePlus ∧
      x.poleMinus = y.poleMinus ∧
      x.vectorPlus = y.vectorPlus ∧
      x.vectorMinus = y.vectorMinus := by
  constructor
  · intro h
    subst y
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩
    cases x
    cases y
    simp_all

@[simp] theorem plus_plus (a b : Vec3 R) :
    star (plusTriplet a) (plusTriplet b) = minusTriplet (cross a b) := by
  apply (eq_iff).2
  simp [star, plusTriplet, minusTriplet]

@[simp] theorem minus_minus (a b : Vec3 R) :
    star (minusTriplet a) (minusTriplet b) = plusTriplet (cross a b) := by
  apply (eq_iff).2
  simp [star, minusTriplet, plusTriplet]

@[simp] theorem plus_minus (a b : Vec3 R) :
    star (plusTriplet a) (minusTriplet b) = plusPole (-dot a b) := by
  apply (eq_iff).2
  simp [star, plusTriplet, minusTriplet, plusPole]

@[simp] theorem minus_plus (a b : Vec3 R) :
    star (minusTriplet a) (plusTriplet b) = minusPole (-dot a b) := by
  apply (eq_iff).2
  simp [star, minusTriplet, plusTriplet, minusPole]

theorem cross_component_zero (a b : Vec3 R) :
    cross a b 0 = a 1 * b 2 - a 2 * b 1 := by
  rfl

theorem cross_component_one (a b : Vec3 R) :
    cross a b 1 = a 2 * b 0 - a 0 * b 2 := by
  rfl

theorem cross_component_two (a b : Vec3 R) :
    cross a b 2 = a 0 * b 1 - a 1 * b 0 := by
  rfl

end ChiralAmplitude

end InfoGeometry.OperatorAlgebra.SplitOctonionChiralTriplet
