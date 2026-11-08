import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Propositional truncation boundary

Lean's `Nonempty` is the native proof-irrelevant carrier for propositional
truncation.  This file exposes its ordinary eliminator and functoriality;
higher truncation levels remain a separate HoTT foundation problem.
-/

namespace InfoGeometry.Spectral.Homotopy.Truncation

abbrev PropTrunc (X : Type*) : Prop := Nonempty X

def unit {X : Type*} : X → PropTrunc X := Nonempty.intro

theorem inhabited_iff {X : Type*} : PropTrunc X ↔ Nonempty X :=
  Iff.rfl

theorem elim {X : Type*} {P : Prop} (h : ∀ _x : X, P) :
    PropTrunc X → P := by
  intro hx
  exact hx.elim h

def map {X Y : Type*} (f : X → Y) : PropTrunc X → PropTrunc Y :=
  fun hx => hx.map f

@[simp] theorem map_unit {X Y : Type*} (f : X → Y) (x : X) :
    map f (unit x) = unit (f x) :=
  rfl

theorem map_comp {X Y Z : Type*} (g : Y → Z) (f : X → Y)
    (x : PropTrunc X) :
    map g (map f x) = map (g ∘ f) x := by
  cases x with
  | intro x => rfl

theorem map_id {X : Type*} (x : PropTrunc X) :
    map id x = x := by
  cases x with
  | intro x => rfl

@[simp] theorem elim_unit {X : Type*} {P : Prop} (h : ∀ _x : X, P)
    (x : X) :
    elim h (unit x) = h x :=
  rfl

theorem map_assoc {W X Y Z : Type*}
    (h : Z → W) (g : Y → Z) (f : X → Y) (x : PropTrunc X) :
    map h (map g (map f x)) = map (h ∘ g ∘ f) x := by
  cases x with
  | intro x => rfl

/-! Set truncation (`trunc 0`) as a quotient with proof-irrelevant targets. -/

/-- The set-truncation of a type, represented by the quotient of its points. -/
abbrev SetTrunc (X : Type*) := Quot (fun _ _ : X => True)

def setTruncMk {X : Type*} (x : X) : SetTrunc X :=
  Quot.mk _ x

@[simp] theorem setTruncMk_eq (X : Type*) (x y : X) :
    setTruncMk x = setTruncMk y := by
  apply Quot.sound
  trivial

def setTruncLift {X Y : Type*} [Subsingleton Y]
    (f : X → Y) : SetTrunc X → Y :=
  Quot.lift f (by
    intro a b _
    exact Subsingleton.elim _ _)

@[simp] theorem setTruncLift_mk {X Y : Type*} [Subsingleton Y]
    (f : X → Y) (x : X) :
    setTruncLift f (setTruncMk x) = f x :=
  by
    simp [setTruncLift, setTruncMk]

theorem setTruncLift_unique {X Y : Type*} [Subsingleton Y]
    (f g : SetTrunc X → Y) : f = g := by
  funext x
  exact Subsingleton.elim _ _

end InfoGeometry.Spectral.Homotopy.Truncation
