import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FinCases

namespace InfoGeometry.Physics.Octonion

variable {A : Type*} [Ring A]

def nextColor : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

def prevColor : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 0
  | 2 => 1

def colorCross (x y : Fin 3 → A) (c : Fin 3) : A :=
  x (nextColor c) * y (prevColor c) -
    x (prevColor c) * y (nextColor c)

def colorDot (x y : Fin 3 → A) : A :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

/-- A chiral Zorn coordinate over an arbitrary, possibly noncommutative ring.
The carrier itself is only equipped with the displayed multiplication; no
associative ring structure is added. -/
structure ChiralZornMatrix (A : Type*) [Ring A] where
  n_plus : A
  n_minus : A
  sigma_plus : Fin 3 → A
  sigma_minus : Fin 3 → A

namespace ChiralZornMatrix

def mul (X Y : ChiralZornMatrix A) : ChiralZornMatrix A where
  n_plus := X.n_plus * Y.n_plus + colorDot X.sigma_plus Y.sigma_minus
  n_minus := colorDot X.sigma_minus Y.sigma_plus + X.n_minus * Y.n_minus
  sigma_plus := fun c =>
    X.n_plus * Y.sigma_plus c + X.sigma_plus c * Y.n_minus -
      colorCross X.sigma_minus Y.sigma_minus c
  sigma_minus := fun c =>
    X.sigma_minus c * Y.n_plus + X.n_minus * Y.sigma_minus c +
      colorCross X.sigma_plus Y.sigma_plus c

instance : Mul (ChiralZornMatrix A) := ⟨mul⟩

instance : One (ChiralZornMatrix A) :=
  ⟨{ n_plus := 1, n_minus := 1, sigma_plus := fun _ => 0, sigma_minus := fun _ => 0 }⟩

instance : Zero (ChiralZornMatrix A) :=
  ⟨{ n_plus := 0, n_minus := 0, sigma_plus := fun _ => 0, sigma_minus := fun _ => 0 }⟩

instance : Add (ChiralZornMatrix A) :=
  ⟨fun X Y => { n_plus := X.n_plus + Y.n_plus, n_minus := X.n_minus + Y.n_minus, sigma_plus := fun c => X.sigma_plus c + Y.sigma_plus c, sigma_minus := fun c => X.sigma_minus c + Y.sigma_minus c }⟩

instance : Neg (ChiralZornMatrix A) :=
  ⟨fun X => { n_plus := -X.n_plus, n_minus := -X.n_minus, sigma_plus := fun c => -X.sigma_plus c, sigma_minus := fun c => -X.sigma_minus c }⟩

def coordEquiv :
    ChiralZornMatrix A ≃ (A × A × (Fin 3 → A) × (Fin 3 → A)) where
  toFun X := (X.n_plus, X.n_minus, X.sigma_plus, X.sigma_minus)
  invFun t :=
    { n_plus := t.1
      n_minus := t.2.1
      sigma_plus := t.2.2.1
      sigma_minus := t.2.2.2 }
  left_inv X := by cases X; rfl
  right_inv t := by rcases t with ⟨np, nm, sp, sm⟩; rfl

instance : AddCommGroup (ChiralZornMatrix A) :=
  Equiv.addCommGroup coordEquiv

instance {R : Type*} [Semiring R] [Module R A] : SMul R (ChiralZornMatrix A) :=
  ⟨fun r X =>
    { n_plus := r • X.n_plus
      n_minus := r • X.n_minus
      sigma_plus := fun c => r • X.sigma_plus c
      sigma_minus := fun c => r • X.sigma_minus c }⟩

instance {R : Type*} [Semiring R] [Module R A] : Module R (ChiralZornMatrix A) :=
  Equiv.module R coordEquiv

theorem single_color_cross_vanishes (x y : Fin 3 → A)
    (h_x : x 1 = 0 ∧ x 2 = 0)
    (h_y : y 1 = 0 ∧ y 2 = 0) (c : Fin 3) :
    colorCross x y c = 0 := by
  rcases h_x with ⟨hx1, hx2⟩
  rcases h_y with ⟨hy1, hy2⟩
  dsimp [colorCross, nextColor, prevColor]
  fin_cases c <;> simp [hx1, hx2, hy1, hy2]

end ChiralZornMatrix
end InfoGeometry.Physics.Octonion
