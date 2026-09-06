import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace InfoGeometry.Algebra.Zorn.G2FanoHammingBridge

open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

/-!
=============================================================================
PART 1: The Fano Plane PG(2, F₂) Geometry
=============================================================================
-/

abbrev FanoPoint := Fin 7
abbrev FanoLine := Fin 7

def fanoLine (l : FanoLine) : Finset FanoPoint :=
  match l with
  | 0 => {0, 1, 3}
  | 1 => {1, 2, 4}
  | 2 => {2, 3, 5}
  | 3 => {3, 4, 6}
  | 4 => {4, 5, 0}
  | 5 => {5, 6, 1}
  | 6 => {6, 0, 2}

def fanoIncidence (p : FanoPoint) (l : FanoLine) : Bool :=
  p ∈ fanoLine l

theorem fano_line_card (l : FanoLine) : (fanoLine l).card = 3 := by
  fin_cases l <;> decide

def fanoPointLines (p : FanoPoint) : Finset FanoLine :=
  Finset.filter (fun l => p ∈ fanoLine l) Finset.univ

theorem fano_point_degree (p : FanoPoint) : (fanoPointLines p).card = 3 := by
  fin_cases p <;> decide

theorem fano_lines_intersect_unique (l₁ l₂ : FanoLine) (h : l₁ ≠ l₂) :
    (fanoLine l₁ ∩ fanoLine l₂).card = 1 := by
  fin_cases l₁ <;> fin_cases l₂ <;> (try contradiction) <;> decide

theorem fano_points_collinear_unique (p₁ p₂ : FanoPoint) (h : p₁ ≠ p₂) :
    (fanoPointLines p₁ ∩ fanoPointLines p₂).card = 1 := by
  fin_cases p₁ <;> fin_cases p₂ <;> (try contradiction) <;> decide

/-!
=============================================================================
PART 2: The [7, 3, 4] Simplex and [7, 4, 3] Hamming Codes
=============================================================================
-/

abbrev BinaryVector7 := Fin 7 → Bool

def hammingWeight (v : BinaryVector7) : ℕ :=
  (Finset.filter (fun i => v i = true) Finset.univ).card

def fanoLineWord (l : FanoLine) : BinaryVector7 :=
  fun p => p ∈ fanoLine l

theorem fanoLineWord_weight (l : FanoLine) : hammingWeight (fanoLineWord l) = 3 := by
  fin_cases l <;> decide

def simplexWord (l : FanoLine) : BinaryVector7 :=
  fun p => ! (p ∈ fanoLine l)

theorem simplexWord_weight (l : FanoLine) : hammingWeight (simplexWord l) = 4 := by
  fin_cases l <;> decide

def isSimplexCodeword (v : BinaryVector7) : Prop :=
  v = (fun _ => false) ∨ ∃ l : FanoLine, v = simplexWord l

def isHammingCodeword (c : BinaryVector7) : Bool :=
  let check0 := ! (c 0 ^^ c 1 ^^ c 3)
  let check1 := ! (c 1 ^^ c 2 ^^ c 4)
  let check2 := ! (c 2 ^^ c 3 ^^ c 5)
  check0 && check1 && check2

def isSimplexDualCodeword (c : BinaryVector7) : Bool :=
  ! (c 0 ^^ c 1 ^^ c 3) &&
  ! (c 1 ^^ c 2 ^^ c 4) &&
  ! (c 2 ^^ c 3 ^^ c 5) &&
  ! (c 3 ^^ c 4 ^^ c 6) &&
  ! (c 4 ^^ c 5 ^^ c 0) &&
  ! (c 5 ^^ c 6 ^^ c 1) &&
  ! (c 6 ^^ c 0 ^^ c 2)

theorem zero_isHammingCodeword : isHammingCodeword (fun _ => false) = true := by
  decide

theorem simplexWord_isHammingCodeword (l : FanoLine) :
    isHammingCodeword (simplexWord l) = true := by
  fin_cases l <;> decide

theorem fanoLine_sum_isHammingCodeword (l₁ l₂ : FanoLine) (h : l₁ ≠ l₂) :
    isHammingCodeword (fun p => fanoLineWord l₁ p ^^ fanoLineWord l₂ p) = true := by
  fin_cases l₁ <;> fin_cases l₂ <;> (try contradiction) <;> decide

theorem fanoLine_sum_weight (l₁ l₂ : FanoLine) (h : l₁ ≠ l₂) :
    hammingWeight (fun p => fanoLineWord l₁ p ^^ fanoLineWord l₂ p) = 4 := by
  fin_cases l₁ <;> fin_cases l₂ <;> (try contradiction) <;> decide

/-!
=============================================================================
PART 3: Cyclotomic Shift Automorphism of the Fano Code
=============================================================================
-/

def shiftPoint (p : FanoPoint) : FanoPoint :=
  ⟨(p.val + 1) % 7, by omega⟩

def shiftLine (l : FanoLine) : FanoLine :=
  ⟨(l.val + 1) % 7, by omega⟩

def cyclotomicShift (v : BinaryVector7) : BinaryVector7 :=
  fun i => v ⟨(i.val + 6) % 7, by omega⟩

theorem cyclotomicShift_fanoLineWord (l : FanoLine) :
    cyclotomicShift (fanoLineWord l) = fanoLineWord (shiftLine l) := by
  fin_cases l <;> decide

theorem cyclotomicShift_simplexWord (l : FanoLine) :
    cyclotomicShift (simplexWord l) = simplexWord (shiftLine l) := by
  fin_cases l <;> decide

/-!
=============================================================================
PART 4: Boolean XOR Distributivity and Step Lemmas
=============================================================================
-/

theorem bool_and_xor (a x y : Bool) : (a && (x ^^ y)) = ((a && x) ^^ (a && y)) := by
  cases a <;> cases x <;> cases y <;> rfl

theorem bool_xor_swap_step (X Y a b : Bool) : ((X ^^ Y) ^^ (a ^^ b)) = ((X ^^ a) ^^ (Y ^^ b)) := by
  cases X <;> cases Y <;> cases a <;> cases b <;> rfl

/-!
=============================================================================
PART 5: Non-Abelian G₂(2) Unipotent Action on the 7-Dimensional Carrier
=============================================================================
-/

def g2UnipotentAction (e : PCExponent) (v : BinaryVector7) : BinaryVector7
  | 0 => v 0 ^^ (e 0 && v 1) ^^ (e 1 && v 2) ^^ (e 2 && v 3) ^^ (e 3 && v 4) ^^ (e 4 && v 5) ^^ (e 5 && v 6)
  | 1 => v 1 ^^ (e 0 && v 2) ^^ (e 1 && v 3) ^^ (e 2 && v 4) ^^ (e 3 && v 5) ^^ (e 4 && v 6)
  | 2 => v 2 ^^ (e 0 && v 3) ^^ (e 1 && v 4) ^^ (e 2 && v 5) ^^ (e 3 && v 6)
  | 3 => v 3 ^^ (e 0 && v 4) ^^ (e 1 && v 5) ^^ (e 2 && v 6)
  | 4 => v 4 ^^ (e 0 && v 5) ^^ (e 1 && v 6)
  | 5 => v 5 ^^ (e 0 && v 6)
  | 6 => v 6

theorem g2UnipotentAction_zero (v : BinaryVector7) :
    g2UnipotentAction zeroPC v = v := by
  funext i
  fin_cases i <;> simp [g2UnipotentAction, zeroPC]

theorem g2UnipotentAction_preserves_last (e : PCExponent) (v : BinaryVector7) :
    g2UnipotentAction e v 6 = v 6 := by
  rfl

theorem g2UnipotentAction_zero_vec (e : PCExponent) :
    g2UnipotentAction e (fun _ => false) = (fun _ => false) := by
  funext i
  fin_cases i <;> simp [g2UnipotentAction]

theorem g2UnipotentAction_add (e : PCExponent) (v w : BinaryVector7) :
    g2UnipotentAction e (fun i => v i ^^ w i) =
      (fun i => g2UnipotentAction e v i ^^ g2UnipotentAction e w i) := by
  funext i
  fin_cases i
  · dsimp [g2UnipotentAction]
    simp only [bool_and_xor]
    rw [bool_xor_swap_step (v 0) (w 0) (e 0 && v 1) (e 0 && w 1)]
    rw [bool_xor_swap_step (v 0 ^^ e 0 && v 1) (w 0 ^^ e 0 && w 1) (e 1 && v 2) (e 1 && w 2)]
    rw [bool_xor_swap_step (v 0 ^^ e 0 && v 1 ^^ e 1 && v 2) (w 0 ^^ e 0 && w 1 ^^ e 1 && w 2) (e 2 && v 3) (e 2 && w 3)]
    rw [bool_xor_swap_step (v 0 ^^ e 0 && v 1 ^^ e 1 && v 2 ^^ e 2 && v 3) (w 0 ^^ e 0 && w 1 ^^ e 1 && w 2 ^^ e 2 && w 3) (e 3 && v 4) (e 3 && w 4)]
    rw [bool_xor_swap_step (v 0 ^^ e 0 && v 1 ^^ e 1 && v 2 ^^ e 2 && v 3 ^^ e 3 && v 4) (w 0 ^^ e 0 && w 1 ^^ e 1 && w 2 ^^ e 2 && w 3 ^^ e 3 && w 4) (e 4 && v 5) (e 4 && w 5)]
    rw [bool_xor_swap_step (v 0 ^^ e 0 && v 1 ^^ e 1 && v 2 ^^ e 2 && v 3 ^^ e 3 && v 4 ^^ e 4 && v 5) (w 0 ^^ e 0 && w 1 ^^ e 1 && w 2 ^^ e 2 && w 3 ^^ e 3 && w 4 ^^ e 4 && w 5) (e 5 && v 6) (e 5 && w 6)]
  · dsimp [g2UnipotentAction]
    simp only [bool_and_xor]
    rw [bool_xor_swap_step (v 1) (w 1) (e 0 && v 2) (e 0 && w 2)]
    rw [bool_xor_swap_step (v 1 ^^ e 0 && v 2) (w 1 ^^ e 0 && w 2) (e 1 && v 3) (e 1 && w 3)]
    rw [bool_xor_swap_step (v 1 ^^ e 0 && v 2 ^^ e 1 && v 3) (w 1 ^^ e 0 && w 2 ^^ e 1 && w 3) (e 2 && v 4) (e 2 && w 4)]
    rw [bool_xor_swap_step (v 1 ^^ e 0 && v 2 ^^ e 1 && v 3 ^^ e 2 && v 4) (w 1 ^^ e 0 && w 2 ^^ e 1 && w 3 ^^ e 2 && w 4) (e 3 && v 5) (e 3 && w 5)]
    rw [bool_xor_swap_step (v 1 ^^ e 0 && v 2 ^^ e 1 && v 3 ^^ e 2 && v 4 ^^ e 3 && v 5) (w 1 ^^ e 0 && w 2 ^^ e 1 && w 3 ^^ e 2 && w 4 ^^ e 3 && w 5) (e 4 && v 6) (e 4 && w 6)]
  · dsimp [g2UnipotentAction]
    simp only [bool_and_xor]
    rw [bool_xor_swap_step (v 2) (w 2) (e 0 && v 3) (e 0 && w 3)]
    rw [bool_xor_swap_step (v 2 ^^ e 0 && v 3) (w 2 ^^ e 0 && w 3) (e 1 && v 4) (e 1 && w 4)]
    rw [bool_xor_swap_step (v 2 ^^ e 0 && v 3 ^^ e 1 && v 4) (w 2 ^^ e 0 && w 3 ^^ e 1 && w 4) (e 2 && v 5) (e 2 && w 5)]
    rw [bool_xor_swap_step (v 2 ^^ e 0 && v 3 ^^ e 1 && v 4 ^^ e 2 && v 5) (w 2 ^^ e 0 && w 3 ^^ e 1 && w 4 ^^ e 2 && w 5) (e 3 && v 6) (e 3 && w 6)]
  · dsimp [g2UnipotentAction]
    simp only [bool_and_xor]
    rw [bool_xor_swap_step (v 3) (w 3) (e 0 && v 4) (e 0 && w 4)]
    rw [bool_xor_swap_step (v 3 ^^ e 0 && v 4) (w 3 ^^ e 0 && w 4) (e 1 && v 5) (e 1 && w 5)]
    rw [bool_xor_swap_step (v 3 ^^ e 0 && v 4 ^^ e 1 && v 5) (w 3 ^^ e 0 && w 4 ^^ e 1 && w 5) (e 2 && v 6) (e 2 && w 6)]
  · dsimp [g2UnipotentAction]
    simp only [bool_and_xor]
    rw [bool_xor_swap_step (v 4) (w 4) (e 0 && v 5) (e 0 && w 5)]
    rw [bool_xor_swap_step (v 4 ^^ e 0 && v 5) (w 4 ^^ e 0 && w 5) (e 1 && v 6) (e 1 && w 6)]
  · dsimp [g2UnipotentAction]
    simp only [bool_and_xor]
    rw [bool_xor_swap_step (v 5) (w 5) (e 0 && v 6) (e 0 && w 6)]
  · dsimp [g2UnipotentAction]

end InfoGeometry.Algebra.Zorn.G2FanoHammingBridge
