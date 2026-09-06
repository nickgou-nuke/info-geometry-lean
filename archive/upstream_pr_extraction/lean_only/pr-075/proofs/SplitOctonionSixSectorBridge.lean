import proofs.SplitOctonionBraidSU3
import proofs.SplitOctonionCircularChiralClosure
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-!
# The six sheet--colour sector of the split-octonion frame

This owner records the combinatorial `2 + 3 + 3` frame only.  It does not
identify the associative six-state operator algebra with split octonions.
The two poles are separate from the six labelled off-diagonal directions.
-/

namespace SplitOctonionSixSectorBridge

abbrev Color3 := Fin 3
abbrev OffDiagonal := Bool × Color3
abbrev Poles := Bool
abbrev Frame := Poles ⊕ OffDiagonal

@[simp] theorem bool_card : Fintype.card Bool = 2 := by
  exact Fintype.card_bool

@[simp] theorem offDiagonal_card : Fintype.card OffDiagonal = 6 := by
  rw [Fintype.card_prod, bool_card]
  norm_num

@[simp] theorem poles_card : Fintype.card Poles = 2 := by
  exact bool_card

@[simp] theorem frame_card : Fintype.card Frame = 8 := by
  rw [Fintype.card_sum, poles_card, offDiagonal_card]

theorem frame_two_plus_three_plus_three :
    Fintype.card Frame = Fintype.card Poles +
      Fintype.card (Bool × Color3) := by
  simp [Frame, OffDiagonal, Poles]

def plusLabel (a : Color3) : OffDiagonal := (true, a)
def minusLabel (a : Color3) : OffDiagonal := (false, a)

@[simp] theorem plusLabel_injective : Function.Injective plusLabel := by
  intro a b h
  exact congrArg Prod.snd h

@[simp] theorem minusLabel_injective : Function.Injective minusLabel := by
  intro a b h
  exact congrArg Prod.snd h

theorem six_labels_are_disjoint :
    (∀ a b : Color3, plusLabel a ≠ minusLabel b) := by
  intro a b h
  have hf := congrArg Prod.fst h
  cases hf

open SplitOctonionCircularChiralClosure

def colorAxis (a : Color3) : SplitOctonionChiralClosure.Vec3 :=
  SplitOctonionChiralClosure.axis a

def plusLane (a : Color3) : SplitOctonionChiralClosure.Zorn := sP (colorAxis a)
def minusLane (a : Color3) : SplitOctonionChiralClosure.Zorn := sM (colorAxis a)

def offDiagonalDirection : OffDiagonal → SplitOctonionChiralClosure.Zorn
  | (true, a) => plusLane a
  | (false, a) => minusLane a

@[simp] theorem offDiagonalDirection_plus (a : Color3) :
    offDiagonalDirection (plusLabel a) = plusLane a := rfl

@[simp] theorem offDiagonalDirection_minus (a : Color3) :
    offDiagonalDirection (minusLabel a) = minusLane a := rfl

theorem plus_plus_closure (a b : Color3) :
    SplitOctonionChiralClosure.mul (plusLane a) (plusLane b) =
      sM (SplitOctonionChiralClosure.cross (colorAxis a) (colorAxis b)) :=
  SplitOctonionChiralClosure.plus_plus_product _ _

theorem minus_minus_closure (a b : Color3) :
    SplitOctonionChiralClosure.mul (minusLane a) (minusLane b) =
      sP (fun i => -SplitOctonionChiralClosure.cross (colorAxis a) (colorAxis b) i) :=
  SplitOctonionChiralClosure.minus_minus_product _ _

theorem plus_minus_returns_positive_pole (a b : Color3) :
    SplitOctonionChiralClosure.mul (plusLane a) (minusLane b) =
      SplitOctonionChiralClosure.smul
        (SplitOctonionChiralClosure.dot (colorAxis a) (colorAxis b)) uP :=
  SplitOctonionChiralClosure.plus_minus_product _ _

theorem minus_plus_returns_negative_pole (a b : Color3) :
    SplitOctonionChiralClosure.mul (minusLane b) (plusLane a) =
      SplitOctonionChiralClosure.smul
        (SplitOctonionChiralClosure.dot (colorAxis b) (colorAxis a)) uM :=
  SplitOctonionChiralClosure.minus_plus_product _ _

theorem pole_lane_actions (a : Color3) :
    SplitOctonionChiralClosure.mul uP (plusLane a) = plusLane a ∧
    SplitOctonionChiralClosure.mul (plusLane a) uM = plusLane a ∧
    SplitOctonionChiralClosure.mul uM (minusLane a) = minusLane a ∧
    SplitOctonionChiralClosure.mul (minusLane a) uP = minusLane a ∧
    SplitOctonionChiralClosure.mul uM (plusLane a) =
      SplitOctonionChiralClosure.zero ∧
    SplitOctonionChiralClosure.mul (plusLane a) uP =
      SplitOctonionChiralClosure.zero ∧
    SplitOctonionChiralClosure.mul uP (minusLane a) =
      SplitOctonionChiralClosure.zero ∧
    SplitOctonionChiralClosure.mul (minusLane a) uM =
      SplitOctonionChiralClosure.zero :=
  SplitOctonionChiralClosure.projector_actions (colorAxis a)

theorem split_octonion_233_product_packet :
    SplitOctonionChiralClosure.add uP uM = unit ∧
    (∀ a b, SplitOctonionChiralClosure.mul (plusLane a) (plusLane b) =
      sM (SplitOctonionChiralClosure.cross (colorAxis a) (colorAxis b))) ∧
    (∀ a b, SplitOctonionChiralClosure.mul (minusLane a) (minusLane b) =
      sP (fun i => -SplitOctonionChiralClosure.cross (colorAxis a) (colorAxis b) i)) ∧
    (∀ a b, SplitOctonionChiralClosure.mul (plusLane a) (minusLane b) =
      SplitOctonionChiralClosure.smul
        (SplitOctonionChiralClosure.dot (colorAxis a) (colorAxis b)) uP) ∧
    (∀ a b, SplitOctonionChiralClosure.mul (minusLane b) (plusLane a) =
      SplitOctonionChiralClosure.smul
        (SplitOctonionChiralClosure.dot (colorAxis b) (colorAxis a)) uM) :=
  ⟨peirce_circular_basis.1, plus_plus_closure, minus_minus_closure,
    plus_minus_returns_positive_pole, minus_plus_returns_negative_pole⟩

end SplitOctonionSixSectorBridge
