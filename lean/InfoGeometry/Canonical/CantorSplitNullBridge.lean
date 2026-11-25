/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitZornNullBoundary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TypeIIIModularCantorSystem

/-!
# Finite Cantor/split-null bridge

This file adds a theorem-safe bridge from finite Cantor addresses to two explicit
split-Zorn null generators.

Closed here:
- an explicit second null generator in the bottom-left Zorn slot;
- a finite bit/address map landing in the split null cone;
- square-zero and self-polar-zero readbacks for both generators;
- the cross-polar hyperbolic pairing between the two isotropic directions.

Out of scope:
- global Cantor-fractal colimits;
- identification of a full GNS null ideal with an infinite split-null colimit;
- `G₂(2)` or exceptional-group boundary-closure theorems.
-/

namespace InfoGeometry.Canonical.CantorSplitNullBridge

open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell
open TypeIIIModularCantorSystem
open TypeIIIModularCantorSystem.BinaryWord
open SplitZornNullBoundary

abbrev FiniteBinaryWord := BinaryWord

/-- Concrete coordinatewise zero in the real Zorn carrier. -/
def zornZero : ZornCell ℝ :=
  { r := 0
    s := 0
    x1 := 0
    x2 := 0
    x3 := 0
    y1 := 0
    y2 := 0
    y3 := 0 }

/-- Local zero instance for the concrete real Zorn carrier used in this bridge. -/
instance instZeroZornCellRealLocal : Zero (ZornCell ℝ) where
  zero := zornZero

@[simp] theorem zornTopRightNull_detZ_local :
    detZ zornTopRightNull = 0 := by
  norm_num [zornTopRightNull, detZ]

theorem zornTopRightNull_ne_zero_local :
    zornTopRightNull ≠ (0 : ZornCell ℝ) := by
  change zornTopRightNull ≠ zornZero
  intro h
  have hx1 : zornTopRightNull.x1 = zornZero.x1 := by
    simpa using congrArg ZornCell.x1 h
  simp [zornTopRightNull, zornZero] at hx1

@[simp] theorem zornTopRightNull_sq_zero_local :
    zornTopRightNull * zornTopRightNull = (0 : ZornCell ℝ) := by
  change mulZ zornTopRightNull zornTopRightNull = zornZero
  simp [zornTopRightNull, zornZero, mulZ]

@[simp] theorem zornTopRightNull_polar_self_zero_local :
    polarZ zornTopRightNull zornTopRightNull = 0 :=
  polarZ_self_of_detZ_zero zornTopRightNull zornTopRightNull_detZ_local

/-- A concrete bottom-left Zorn null generator over `ℝ`. -/
def zornBottomLeftNull : ZornCell ℝ where
  r := 0
  s := 0
  x1 := 0
  x2 := 0
  x3 := 0
  y1 := 1
  y2 := 0
  y3 := 0

@[simp] theorem zornBottomLeftNull_detZ :
    detZ zornBottomLeftNull = 0 := by
  norm_num [zornBottomLeftNull, detZ]

/-- The bottom-left Zorn null generator is nonzero. -/
theorem zornBottomLeftNull_ne_zero :
    zornBottomLeftNull ≠ (0 : ZornCell ℝ) := by
  change zornBottomLeftNull ≠ zornZero
  intro h
  have hy1 : zornBottomLeftNull.y1 = zornZero.y1 := by
    simpa using congrArg ZornCell.y1 h
  simp [zornBottomLeftNull, zornZero] at hy1

/-- The bottom-left Zorn null generator is square-zero. -/
@[simp] theorem zornBottomLeftNull_sq_zero :
    zornBottomLeftNull * zornBottomLeftNull = (0 : ZornCell ℝ) := by
  change mulZ zornBottomLeftNull zornBottomLeftNull = zornZero
  simp [zornBottomLeftNull, zornZero, mulZ]

/-- The bottom-left Zorn null generator is self-orthogonal for the Zorn polar form. -/
@[simp] theorem zornBottomLeftNull_polar_self_zero :
    polarZ zornBottomLeftNull zornBottomLeftNull = 0 :=
  polarZ_self_of_detZ_zero zornBottomLeftNull zornBottomLeftNull_detZ

/-- The two explicit bit generators for the split-null bridge. -/
def bitNullGenerator : Bool → ZornCell ℝ
  | false => zornTopRightNull
  | true => zornBottomLeftNull

@[simp] theorem bitNullGenerator_false :
    bitNullGenerator false = zornTopRightNull := rfl

@[simp] theorem bitNullGenerator_true :
    bitNullGenerator true = zornBottomLeftNull := rfl

theorem bitNullGenerator_ne_zero (b : Bool) :
    bitNullGenerator b ≠ (0 : ZornCell ℝ) := by
  cases b <;> simp [bitNullGenerator, zornTopRightNull_ne_zero_local, zornBottomLeftNull_ne_zero]

@[simp] theorem bitNullGenerator_detZ_zero (b : Bool) :
    detZ (bitNullGenerator b) = 0 := by
  cases b <;> simp [bitNullGenerator]

@[simp] theorem bitNullGenerator_sq_zero (b : Bool) :
    bitNullGenerator b * bitNullGenerator b = (0 : ZornCell ℝ) := by
  cases b <;> simp [bitNullGenerator, zornTopRightNull_sq_zero_local]

@[simp] theorem bitNullGenerator_polar_self_zero (b : Bool) :
    polarZ (bitNullGenerator b) (bitNullGenerator b) = 0 := by
  cases b <;> simp [bitNullGenerator, zornTopRightNull_polar_self_zero_local]

/-- Finite Cantor address readout: use the last branch bit as the null-generator selector. -/
def addressNullGenerator (w : FiniteBinaryWord) : ZornCell ℝ :=
  match w.getLast? with
  | some b => bitNullGenerator b
  | none => 0

@[simp] theorem addressNullGenerator_nil :
    addressNullGenerator [] = (0 : ZornCell ℝ) := rfl

@[simp] theorem addressNullGenerator_child (w : FiniteBinaryWord) (b : Bool) :
    addressNullGenerator (child w b) = bitNullGenerator b := by
  simp [addressNullGenerator, child]

/-- Every one-step child address lands in a nonzero split-null generator. -/
theorem addressNullGenerator_child_ne_zero (w : FiniteBinaryWord) (b : Bool) :
    addressNullGenerator (child w b) ≠ (0 : ZornCell ℝ) := by
  simpa [addressNullGenerator_child] using bitNullGenerator_ne_zero b

/-- Every one-step child address lands in the split null cone. -/
theorem addressNullGenerator_child_detZ_zero (w : FiniteBinaryWord) (b : Bool) :
    detZ (addressNullGenerator (child w b)) = 0 := by
  simp [addressNullGenerator_child]

/-- Every one-step child address is square-zero. -/
theorem addressNullGenerator_child_sq_zero (w : FiniteBinaryWord) (b : Bool) :
    addressNullGenerator (child w b) *
      addressNullGenerator (child w b) = (0 : ZornCell ℝ) := by
  simp [addressNullGenerator_child]

/-- Every one-step child address is self-orthogonal for the split polar form. -/
theorem addressNullGenerator_child_polar_self_zero (w : FiniteBinaryWord) (b : Bool) :
    polarZ (addressNullGenerator (child w b))
      (addressNullGenerator (child w b)) = 0 := by
  simp [addressNullGenerator_child]

/-! ### Prefix-faithful address map into a Zorn null line

Binary-tree heap indices are embedded in the `x1` axis of the Zorn carrier, a
null line for `detZ`. Appending a bit follows the corresponding child step. -/

/-- Heap index of a finite binary word, with root index `1`. -/
def addressIndex : FiniteBinaryWord → ℕ :=
  List.foldl (fun n b => 2 * n + (if b then 1 else 0)) 1

/-- A word-dependent point on the top-right Zorn null line. -/
def addressZornNullCell (w : FiniteBinaryWord) : ZornCell ℝ where
  r := 0
  s := 0
  x1 := (addressIndex w : ℝ)
  x2 := 0
  x3 := 0
  y1 := 0
  y2 := 0
  y3 := 0

theorem addressIndex_child (w : FiniteBinaryWord) (b : Bool) :
    addressIndex (child w b) = 2 * addressIndex w + (if b then 1 else 0) := by
  simp [addressIndex, child, List.foldl_append]

theorem addressZornNullCell_child_x1 (w : FiniteBinaryWord) (b : Bool) :
    (addressZornNullCell (child w b)).x1 =
      (2 * addressIndex w + (if b then 1 else 0) : ℕ) := by
  simp [addressZornNullCell, addressIndex_child]

theorem addressZornNullCell_detZ_zero (w : FiniteBinaryWord) :
    detZ (addressZornNullCell w) = 0 := by
  simp [addressZornNullCell, detZ]

theorem addressZornNullCell_sq_zero (w : FiniteBinaryWord) :
    addressZornNullCell w * addressZornNullCell w = (0 : ZornCell ℝ) := by
  change mulZ (addressZornNullCell w) (addressZornNullCell w) = zornZero
  simp [addressZornNullCell, zornZero, mulZ]

theorem addressZornNullCell_children_distinct (w : FiniteBinaryWord) :
    addressZornNullCell (child w false) ≠ addressZornNullCell (child w true) := by
  intro h
  have hx := congrArg ZornCell.x1 h
  rw [addressZornNullCell_child_x1, addressZornNullCell_child_x1] at hx
  have hn : (2 * addressIndex w : ℕ) = 2 * addressIndex w + 1 := by
    exact_mod_cast hx
  omega

/-- Parity of all branch bits in a finite address. -/
def addressParity : FiniteBinaryWord → Bool
  | [] => false
  | b :: w => Bool.xor b (addressParity w)

/-- Appending a branch updates address parity by xor with that branch. -/
theorem addressParity_child (w : FiniteBinaryWord) (b : Bool) :
    addressParity (child w b) = Bool.xor (addressParity w) b := by
  induction w with
  | nil => simp [addressParity, child]
  | cons a w ih =>
      simp only [child, List.cons_append, addressParity]
      have ih' : addressParity (w ++ [b]) = Bool.xor (addressParity w) b := by
        simpa [child] using ih
      rw [ih']
      cases a <;> cases addressParity w <;> cases b <;> rfl

/-- A recursive address readout into the two Zorn null directions.

Unlike `addressNullGenerator`, this readout depends on the parity of the entire
word and updates by a specified branch transition.  It is intentionally only a
two-state quotient of addresses; it does not claim injectivity. -/
def parityAddressNullGenerator (w : FiniteBinaryWord) : ZornCell ℝ :=
  bitNullGenerator (addressParity w)

/-- Appending a bit intertwines the Zorn readout with its parity transition. -/
theorem parityAddressNullGenerator_child (w : FiniteBinaryWord) (b : Bool) :
    parityAddressNullGenerator (child w b) =
      bitNullGenerator (Bool.xor (addressParity w) b) := by
  simp [parityAddressNullGenerator, addressParity_child]

/-- Every parity-address readout remains in the split null cone. -/
theorem parityAddressNullGenerator_detZ_zero (w : FiniteBinaryWord) :
    detZ (parityAddressNullGenerator w) = 0 := by
  simp [parityAddressNullGenerator]

/-- Every parity-address readout remains square-zero. -/
theorem parityAddressNullGenerator_sq_zero (w : FiniteBinaryWord) :
    parityAddressNullGenerator w * parityAddressNullGenerator w =
      (0 : ZornCell ℝ) := by
  simp [parityAddressNullGenerator]

/-- The two bit-controlled split-null directions form a concrete hyperbolic pair. -/
@[simp] theorem topRight_bottomLeft_polar_pair :
    polarZ zornTopRightNull zornBottomLeftNull = -1 := by
  norm_num [polarZ, addZ, detZ, zornTopRightNull, zornBottomLeftNull]

/-- The false/true child generators form the same hyperbolic pair. -/
@[simp] theorem child_false_true_polar_pair (w : FiniteBinaryWord) :
    polarZ (addressNullGenerator (child w false))
      (addressNullGenerator (child w true)) = -1 := by
  simp [addressNullGenerator_child, topRight_bottomLeft_polar_pair]

/-- Closed finite packet for the Cantor/split-null bridge. -/
theorem cantor_split_null_bridge_packet (w : FiniteBinaryWord) :
    addressNullGenerator (child w false) ≠ (0 : ZornCell ℝ) ∧
      addressNullGenerator (child w true) ≠ (0 : ZornCell ℝ) ∧
      detZ (addressNullGenerator (child w false)) = 0 ∧
      detZ (addressNullGenerator (child w true)) = 0 ∧
      addressNullGenerator (child w false) *
          addressNullGenerator (child w false) = (0 : ZornCell ℝ) ∧
      addressNullGenerator (child w true) *
          addressNullGenerator (child w true) = (0 : ZornCell ℝ) ∧
      polarZ (addressNullGenerator (child w false))
          (addressNullGenerator (child w false)) = 0 ∧
      polarZ (addressNullGenerator (child w true))
          (addressNullGenerator (child w true)) = 0 ∧
      polarZ (addressNullGenerator (child w false))
          (addressNullGenerator (child w true)) = -1 := by
  exact ⟨addressNullGenerator_child_ne_zero w false,
    addressNullGenerator_child_ne_zero w true,
    addressNullGenerator_child_detZ_zero w false,
    addressNullGenerator_child_detZ_zero w true,
    addressNullGenerator_child_sq_zero w false,
    addressNullGenerator_child_sq_zero w true,
    addressNullGenerator_child_polar_self_zero w false,
    addressNullGenerator_child_polar_self_zero w true,
    child_false_true_polar_pair w⟩

end InfoGeometry.Canonical.CantorSplitNullBridge
