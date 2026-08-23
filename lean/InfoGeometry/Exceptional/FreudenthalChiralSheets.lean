import InfoGeometry.Exceptional.FreudenthalHeisenberg

/-!
# Tagged Freudenthal chiral sheets

The five-grading of split `E₈` requires two independent copies of the
Freudenthal 56-dimensional carrier in grades `-1` and `+1`.  A plain pair of
`abbrev`s would erase this distinction definitionally in Lean, so this owner
introduces an explicit grade tag while reusing the already proved Freudenthal
Heisenberg Lie algebra for each same-sign sector.

This file does not define the mixed bracket `[-1,+1] → 0`; that bracket must
land in the actual kernel-closed `𝔢₇(7) ⊕ ℝH` carrier, which is not yet
constructed in the repository.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

open FreudenthalCharge

/-- The two macro-polarized grade-one sheets in the exceptional five-grading. -/
inductive FreudenthalSheetSign where
  | minus
  | plus
deriving DecidableEq, Repr

/-- A Freudenthal charge tagged by its five-grade sheet.  The tag is part of
the type, so positive and negative sheets cannot be silently interchanged. -/
@[ext]
structure FreudenthalSheet
    (sign : FreudenthalSheetSign)
    (J : Type*) [AddCommGroup J] [Module ℝ J] where
  charge : FreudenthalCharge J

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

abbrev FreudenthalMinus := FreudenthalSheet FreudenthalSheetSign.minus J
abbrev FreudenthalPlus := FreudenthalSheet FreudenthalSheetSign.plus J

/-- Canonical tagged negative-sheet copy of a Freudenthal charge. -/
def toMinus (Q : FreudenthalCharge J) : FreudenthalMinus := ⟨Q⟩

/-- Canonical tagged positive-sheet copy of a Freudenthal charge. -/
def toPlus (Q : FreudenthalCharge J) : FreudenthalPlus := ⟨Q⟩

@[simp] theorem toMinus_charge (Q : FreudenthalCharge J) : (toMinus Q).charge = Q := rfl
@[simp] theorem toPlus_charge (Q : FreudenthalCharge J) : (toPlus Q).charge = Q := rfl

/-- Embed a tagged sheet element into the existing genuine Freudenthal
Heisenberg algebra with zero central coordinate. -/
def sheetToHeisenberg
    (D : CubicJordanDatum J) {sign : FreudenthalSheetSign}
    (X : FreudenthalSheet sign J) : FreudenthalHeisenberg D :=
  (X.charge, 0)

@[simp] theorem sheetToHeisenberg_charge
    (D : CubicJordanDatum J) {sign : FreudenthalSheetSign}
    (X : FreudenthalSheet sign J) :
    (sheetToHeisenberg D X).1 = X.charge := rfl

@[simp] theorem sheetToHeisenberg_center
    (D : CubicJordanDatum J) {sign : FreudenthalSheetSign}
    (X : FreudenthalSheet sign J) :
    (sheetToHeisenberg D X).2 = 0 := rfl

/-- Same-sheet bracket, evaluated in the already kernel-closed Heisenberg Lie
algebra, lands exactly in its one-dimensional central grade. -/
theorem sameSheet_bracket_eq_center
    (D : CubicJordanDatum J) {sign : FreudenthalSheetSign}
    (X Y : FreudenthalSheet sign J) :
    ⁅sheetToHeisenberg D X, sheetToHeisenberg D Y⁆ =
      heisenbergCenter D (symplecticForm D X.charge Y.charge) := by
  exact bracket_eq_center D (sheetToHeisenberg D X) (sheetToHeisenberg D Y)

/-- Positive macro-sheet Heisenberg closure: `g₊₁ × g₊₁ → g₊₂`. -/
theorem freudenthal_plus_heisenberg_bracket
    (D : CubicJordanDatum J) (X Y : FreudenthalPlus) :
    ⁅sheetToHeisenberg D X, sheetToHeisenberg D Y⁆ =
      heisenbergCenter D (symplecticForm D X.charge Y.charge) :=
  sameSheet_bracket_eq_center D X Y

/-- Negative macro-sheet Heisenberg closure: `g₋₁ × g₋₁ → g₋₂`. -/
theorem freudenthal_minus_heisenberg_bracket
    (D : CubicJordanDatum J) (X Y : FreudenthalMinus) :
    ⁅sheetToHeisenberg D X, sheetToHeisenberg D Y⁆ =
      heisenbergCenter D (symplecticForm D X.charge Y.charge) :=
  sameSheet_bracket_eq_center D X Y

/-- Each tagged sheet is faithfully represented by the charge component of
its Heisenberg embedding. -/
theorem sheetToHeisenberg_injective
    (D : CubicJordanDatum J) {sign : FreudenthalSheetSign} :
    Function.Injective (sheetToHeisenberg D : FreudenthalSheet sign J → FreudenthalHeisenberg D) := by
  intro X Y h
  apply FreudenthalSheet.ext
  exact congrArg Prod.fst h

end InfoGeometry.Exceptional.Freudenthal
