import InfoGeometry.Algebra.Zorn.BasisTable

/-!
# Native three-colour brackets for the Zorn basis

This is the exact bracket readout of the native Zorn multiplication table.
It deliberately does not install a Lie or Lie-superalgebra instance: the full
Zorn carrier is nonassociative.  The fixed-colour associative cores are handled
separately by `Basis8.fixedColourEmbedding_mul`.
-/

namespace InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

def zeroCell : ZornCell ℤ :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

def addCell (X Y : ZornCell ℤ) : ZornCell ℤ :=
  ⟨X.r + Y.r, X.s + Y.s, X.x1 + Y.x1, X.x2 + Y.x2, X.x3 + Y.x3,
    X.y1 + Y.y1, X.y2 + Y.y2, X.y3 + Y.y3⟩

def negCell (X : ZornCell ℤ) : ZornCell ℤ :=
  ⟨-X.r, -X.s, -X.x1, -X.x2, -X.x3, -X.y1, -X.y2, -X.y3⟩

def subCell (X Y : ZornCell ℤ) : ZornCell ℤ :=
  addCell X (negCell Y)

def commutator (X Y : ZornCell ℤ) : ZornCell ℤ :=
  subCell (X * Y) (Y * X)

def anticommutator (X Y : ZornCell ℤ) : ZornCell ℤ :=
  addCell (X * Y) (Y * X)

def sigmaMinus (i : Fin 3) : ZornCell ℤ :=
  match i with
  | 0 => cell v1
  | 1 => cell v2
  | 2 => cell v3

def sigmaPlus (i : Fin 3) : ZornCell ℤ :=
  match i with
  | 0 => cell u1
  | 1 => cell u2
  | 2 => cell u3

@[simp] theorem sigmaMinus_0_1_commutator :
    commutator (sigmaMinus 0) (sigmaMinus 1) = negCell (addCell (cell u3) (cell u3)) := by
  decide

@[simp] theorem sigmaMinus_0_2_commutator :
    commutator (sigmaMinus 0) (sigmaMinus 2) = addCell (cell u2) (cell u2) := by
  decide

@[simp] theorem sigmaMinus_1_2_commutator :
    commutator (sigmaMinus 1) (sigmaMinus 2) = negCell (addCell (cell u1) (cell u1)) := by
  decide

@[simp] theorem sigmaMinus_0_1_anticommutator :
    anticommutator (sigmaMinus 0) (sigmaMinus 1) = zeroCell := by
  decide

@[simp] theorem sigmaMinus_0_2_anticommutator :
    anticommutator (sigmaMinus 0) (sigmaMinus 2) = zeroCell := by
  decide

@[simp] theorem sigmaMinus_1_2_anticommutator :
    anticommutator (sigmaMinus 1) (sigmaMinus 2) = zeroCell := by
  decide

theorem sigmaMinus_anticommutator (i j : Fin 3) :
    anticommutator (sigmaMinus i) (sigmaMinus j) = zeroCell := by
  fin_cases i <;> fin_cases j <;> decide

theorem sigmaMinus_commutator_diagonal (i : Fin 3) :
    commutator (sigmaMinus i) (sigmaMinus i) = zeroCell := by
  fin_cases i <;> decide

def sigmaMinusCommutatorExpected (i j : Fin 3) : ZornCell ℤ :=
  if i = 0 ∧ j = 1 then negCell (addCell (cell u3) (cell u3)) else
  if i = 1 ∧ j = 0 then addCell (cell u3) (cell u3) else
  if i = 0 ∧ j = 2 then addCell (cell u2) (cell u2) else
  if i = 2 ∧ j = 0 then negCell (addCell (cell u2) (cell u2)) else
  if i = 1 ∧ j = 2 then negCell (addCell (cell u1) (cell u1)) else
  if i = 2 ∧ j = 1 then addCell (cell u1) (cell u1) else
    zeroCell

theorem sigmaMinus_commutator (i j : Fin 3) :
    commutator (sigmaMinus i) (sigmaMinus j) =
      sigmaMinusCommutatorExpected i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem sigmaPlus_sigmaMinus_anticommutator (i j : Fin 3) :
    anticommutator (sigmaPlus i) (sigmaMinus j) =
      if i = j then addCell (cell e11) (cell e22) else zeroCell := by
  fin_cases i <;> fin_cases j <;> decide

theorem sigmaPlus_sigmaMinus_commutator (i j : Fin 3) :
    commutator (sigmaPlus i) (sigmaMinus j) =
      if i = j then subCell (cell e11) (cell e22) else zeroCell := by
  fin_cases i <;> fin_cases j <;> decide

end InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell.Basis8
