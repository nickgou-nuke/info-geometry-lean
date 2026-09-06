import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Hexagonal six-root combinatorics

This owner contains only the finite label combinatorics of the six-state cell.
It identifies `ZMod 6` with a two-sheet, three-colour carrier, and records the
colour rotation and Pin-glide reflection on those labels.  Complex roots,
matrices, characteristic polynomials, topology, and Hamiltonians belong to
later bridge owners.
-/

namespace HexagonalSixRootTiling

abbrev HexIndex := ZMod 6
abbrev HexColor := ZMod 3

inductive HexSheet
  | positive
  | negative
  deriving DecidableEq, Fintype

/-- The positive sheet is the alternating cycle `0, 2, 4`. -/
def positiveVertex (a : HexColor) : HexIndex := 2 * (a.val : HexIndex)

/-- The negative sheet is the alternating cycle `3, 5, 1`. -/
def negativeVertex (a : HexColor) : HexIndex := positiveVertex a + 3

/-- Sheet parity of a sixfold label. -/
def sheetOf (n : HexIndex) : HexSheet :=
  if n.val % 2 = 0 then .positive else .negative

/-- Colour coordinate in the alternating ordering on each sheet. -/
def colorOf (n : HexIndex) : HexColor :=
  match n.val with
  | 0 | 3 => 0
  | 2 | 5 => 1
  | _ => 2

def vertexOf : HexSheet × HexColor → HexIndex
  | (.positive, a) => positiveVertex a
  | (.negative, a) => negativeVertex a

theorem vertexOf_sheet_color (n : HexIndex) :
    vertexOf (sheetOf n, colorOf n) = n := by
  fin_cases n <;> decide

theorem sheet_color_vertexOf (p : HexSheet × HexColor) :
    (sheetOf (vertexOf p), colorOf (vertexOf p)) = p := by
  rcases p with ⟨s, a⟩
  cases s <;> fin_cases a <;> decide

/-- Canonical Chinese-remainder labelling of six vertices by sheet and colour. -/
def sheetColorEquiv : HexIndex ≃ HexSheet × HexColor where
  toFun n := (sheetOf n, colorOf n)
  invFun := vertexOf
  left_inv := vertexOf_sheet_color
  right_inv := sheet_color_vertexOf

@[simp] theorem sheetColorEquiv_symm_positive (a : HexColor) :
    sheetColorEquiv.symm (.positive, a) = positiveVertex a := rfl

@[simp] theorem sheetColorEquiv_symm_negative (a : HexColor) :
    sheetColorEquiv.symm (.negative, a) = negativeVertex a := rfl

theorem positiveVertex_ne_negativeVertex (a b : HexColor) :
    positiveVertex a ≠ negativeVertex b := by
  fin_cases a <;> fin_cases b <;> decide

theorem existsUnique_sheet_color (n : HexIndex) :
    ∃! p : HexSheet × HexColor, vertexOf p = n := by
  refine ⟨sheetColorEquiv n, sheetColorEquiv.symm_apply_apply n, ?_⟩
  intro p hp
  apply sheetColorEquiv.symm.injective
  simpa using hp

def positiveCycle : Finset HexIndex := Finset.univ.image positiveVertex
def negativeCycle : Finset HexIndex := Finset.univ.image negativeVertex

theorem positiveCycle_eq : positiveCycle = {0, 2, 4} := by decide
theorem negativeCycle_eq : negativeCycle = {1, 3, 5} := by decide

theorem cycles_disjoint : Disjoint positiveCycle negativeCycle := by decide

theorem cycles_cover : positiveCycle ∪ negativeCycle = Finset.univ := by decide

/-- Rotation by one colour step, i.e. two hexagonal vertices. -/
def colorRotate (n : HexIndex) : HexIndex := n + 2

@[simp] theorem colorRotate_positiveVertex (a : HexColor) :
    colorRotate (positiveVertex a) = positiveVertex (a + 1) := by
  fin_cases a <;> decide

@[simp] theorem colorRotate_negativeVertex (a : HexColor) :
    colorRotate (negativeVertex a) = negativeVertex (a + 1) := by
  fin_cases a <;> decide

theorem colorRotate_three (n : HexIndex) :
    colorRotate (colorRotate (colorRotate n)) = n := by
  fin_cases n <;> decide

/-- Pin-glide reflection on the six cyclotomic labels. -/
def hexReflect (n : HexIndex) : HexIndex := 3 - n

theorem hexReflect_involutive : Function.Involutive hexReflect := by
  intro n
  simp [hexReflect]

@[simp] theorem hexReflect_positiveVertex (a : HexColor) :
    hexReflect (positiveVertex a) = negativeVertex (-a) := by
  fin_cases a <;> decide

@[simp] theorem hexReflect_negativeVertex (a : HexColor) :
    hexReflect (negativeVertex a) = positiveVertex (-a) := by
  fin_cases a <;> decide

theorem hexReflect_no_fixed (n : HexIndex) : hexReflect n ≠ n := by
  fin_cases n <;> decide

theorem hexReflect_orbits :
    hexReflect 0 = 3 ∧ hexReflect 3 = 0 ∧
    hexReflect 1 = 2 ∧ hexReflect 2 = 1 ∧
    hexReflect 4 = 5 ∧ hexReflect 5 = 4 := by
  decide

/-- Finite dihedral compatibility: reflection reverses colour rotation. -/
theorem hexReflect_colorRotate (n : HexIndex) :
    hexReflect (colorRotate n) = colorRotate (colorRotate (hexReflect n)) := by
  fin_cases n <;> decide

theorem sheetColorEquiv_reflection_positive (a : HexColor) :
    sheetColorEquiv (hexReflect (positiveVertex a)) = (.negative, -a) := by
  fin_cases a <;> decide

theorem sheetColorEquiv_reflection_negative (a : HexColor) :
    sheetColorEquiv (hexReflect (negativeVertex a)) = (.positive, -a) := by
  fin_cases a <;> decide

end HexagonalSixRootTiling
