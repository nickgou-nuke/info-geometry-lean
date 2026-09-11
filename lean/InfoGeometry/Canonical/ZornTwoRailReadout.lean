import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Real two-rail Zorn readout

This owner is the proved coordinate bridge from two real `(1+3)` payloads to
the native Zorn matrix carrier.  It asserts no associative product or spinor
identification; those require separate intertwining theorems.
-/

namespace InfoGeometry.Canonical.ZornTwoRailReadout

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix

variable {R : Type*} [CommRing R]

def uPlus : ZornMatrix R :=
  { a := 1, v := fun _ => 0, w := fun _ => 0, b := 0 }

def uMinus : ZornMatrix R :=
  { a := 0, v := fun _ => 0, w := fun _ => 0, b := 1 }

def sPlus (i : Fin 3) : ZornMatrix R :=
  { a := 0, v := Vec3.basis i, w := fun _ => 0, b := 0 }

def sMinus (i : Fin 3) : ZornMatrix R :=
  { a := 0, v := fun _ => 0, w := Vec3.basis i, b := 0 }

def twoRail (Pplus Pminus : Fin 4 → R) : ZornMatrix R :=
  { a := Pplus 0
    v := fun i => Pplus (i.succ)
    w := fun i => Pminus (i.succ)
    b := Pminus 0 }

@[simp] theorem twoRail_a (Pplus Pminus : Fin 4 → R) :
    (twoRail Pplus Pminus).a = Pplus 0 := rfl

@[simp] theorem twoRail_b (Pplus Pminus : Fin 4 → R) :
    (twoRail Pplus Pminus).b = Pminus 0 := rfl

@[simp] theorem twoRail_v (Pplus Pminus : Fin 4 → R) (i : Fin 3) :
    (twoRail Pplus Pminus).v i = Pplus (i.succ) := rfl

@[simp] theorem twoRail_w (Pplus Pminus : Fin 4 → R) (i : Fin 3) :
    (twoRail Pplus Pminus).w i = Pminus (i.succ) := rfl

theorem twoRail_injective
    (Pplus Pminus Qplus Qminus : Fin 4 → R)
    (h : twoRail Pplus Pminus = twoRail Qplus Qminus) :
    Pplus = Qplus ∧ Pminus = Qminus := by
  constructor
  · funext i
    fin_cases i
    · exact congrArg (fun Z : ZornMatrix R => Z.a) h
    · exact congrArg (fun Z : ZornMatrix R => Z.v 0) h
    · exact congrArg (fun Z : ZornMatrix R => Z.v 1) h
    · exact congrArg (fun Z : ZornMatrix R => Z.v 2) h
  · funext i
    fin_cases i
    · exact congrArg (fun Z : ZornMatrix R => Z.b) h
    · exact congrArg (fun Z : ZornMatrix R => Z.w 0) h
    · exact congrArg (fun Z : ZornMatrix R => Z.w 1) h
    · exact congrArg (fun Z : ZornMatrix R => Z.w 2) h

theorem twoRail_minus_injective :
    Function.Injective (fun P : Fin 4 → R => twoRail P P) := by
  intro P Q h
  exact (twoRail_injective P P Q Q h).1

end InfoGeometry.Canonical.ZornTwoRailReadout
