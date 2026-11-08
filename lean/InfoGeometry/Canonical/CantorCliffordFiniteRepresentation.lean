import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.CantorCliffordFiniteRepresentation

Finite binary Cantor endpoint operations with closed switch/tilt laws.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCliffordFiniteRepresentation

/-- Binary words of length `n`. -/
abbrev Word (n : ℕ) : Type := Fin n → Bool

/-- Endpoint function space. -/
abbrev Fn (n : ℕ) (α : Type*) : Type _ := Word n → α

/-- Flip one bit of a binary word. -/
def flipBit {n : ℕ} (j : Fin n) (w : Word n) : Word n :=
  fun k => if k = j then !w k else w k

/-- Bit flip is involutive. -/
theorem flipBit_involutive {n : ℕ} (j : Fin n) (w : Word n) :
    flipBit j (flipBit j w) = w := by
  funext k
  by_cases h : k = j <;> simp [flipBit, h]

/-- Switch operator by precomposition with bit flip. -/
def switch {n : ℕ} {α : Type*} (j : Fin n) (f : Fn n α) : Fn n α :=
  fun w => f (flipBit j w)

/-- Switch squares to identity. -/
theorem switch_sq {n : ℕ} {α : Type*} (j : Fin n) (f : Fn n α) :
    switch j (switch j f) = f := by
  funext w
  simp [switch, flipBit_involutive]

/-- Boolean sign action. -/
def boolSignAct {α : Type*} [Neg α] (b : Bool) (x : α) : α :=
  if b then -x else x

/-- Boolean sign action is involutive when negation is involutive. -/
theorem boolSignAct_sq {α : Type*} [InvolutiveNeg α] (b : Bool) (x : α) :
    boolSignAct b (boolSignAct b x) = x := by
  cases b <;> simp [boolSignAct]

/-- Tilt/sign operator at one coordinate. -/
def tilt {n : ℕ} {α : Type*} [Neg α] (j : Fin n) (f : Fn n α) : Fn n α :=
  fun w => boolSignAct (w j) (f w)

/-- Tilt squares to identity. -/
theorem tilt_sq {n : ℕ} {α : Type*} [InvolutiveNeg α] (j : Fin n) (f : Fn n α) :
    tilt j (tilt j f) = f := by
  funext w
  simp [tilt, boolSignAct_sq]

end InfoGeometry.Canonical.CantorCliffordFiniteRepresentation
