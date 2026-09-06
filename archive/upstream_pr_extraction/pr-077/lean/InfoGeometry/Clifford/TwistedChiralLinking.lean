import Mathlib.Tactic

/-!
# Twisted chiral linking algebra

This is a small algebraic layer over an existing associative carrier.  It
records two idempotent corners and their off-diagonal linking spaces.  It does
not assert that the carrier is a Clifford algebra or that a twist is geometric.
-/

namespace InfoGeometry.Clifford.TwistedChiralLinking

variable {A : Type*} [Ring A]

structure ProjectionPair (A : Type*) [Ring A] where
  plus : A
  plus_idem : plus * plus = plus

def minus (P : ProjectionPair A) : A := 1 - P.plus

theorem minus_idem (P : ProjectionPair A) :
    minus P * minus P = minus P := by
  dsimp [minus]
  rw [sub_mul, one_mul, mul_sub, mul_one, P.plus_idem]
  noncomm_ring

def PlusCorner (P : ProjectionPair A) :=
  {x : A // P.plus * x = x ∧ x * P.plus = x}

def MinusCorner (P : ProjectionPair A) :=
  {x : A // minus P * x = x ∧ x * minus P = x}

def PlusMinusCorner (P : ProjectionPair A) :=
  {x : A // P.plus * x = x ∧ x * minus P = x}

def MinusPlusCorner (P : ProjectionPair A) :=
  {x : A // minus P * x = x ∧ x * P.plus = x}

def plusCornerMul (P : ProjectionPair A)
    (x y : PlusCorner P) :
    PlusCorner P := by
  refine ⟨x.1 * y.1, ?_⟩
  constructor
  · calc
      P.plus * (x.1 * y.1) = (P.plus * x.1) * y.1 := by rw [mul_assoc]
      _ = x.1 * y.1 := by rw [x.2.1]
  · calc
      (x.1 * y.1) * P.plus = x.1 * (y.1 * P.plus) := by rw [mul_assoc]
      _ = x.1 * y.1 := by rw [y.2.2]

def minusCornerMul (P : ProjectionPair A)
    (x y : MinusCorner P) :
    MinusCorner P := by
  refine ⟨x.1 * y.1, ?_⟩
  constructor
  · calc
      minus P * (x.1 * y.1) = (minus P * x.1) * y.1 := by rw [mul_assoc]
      _ = x.1 * y.1 := by rw [x.2.1]
  · calc
      (x.1 * y.1) * minus P = x.1 * (y.1 * minus P) := by rw [mul_assoc]
      _ = x.1 * y.1 := by rw [y.2.2]

def linkingMatrix
    (P : ProjectionPair A)
    (xpp : PlusCorner P) (xpm : PlusMinusCorner P)
    (xmp : MinusPlusCorner P) (xmm : MinusCorner P) :
    Matrix (Fin 2) (Fin 2) A :=
  !![xpp.1, xpm.1; xmp.1, xmm.1]

structure ChiralTwist (P : ProjectionPair A) where
  toMinus : PlusCorner P → MinusCorner P
  toPlus : MinusCorner P → PlusCorner P
  left_inverse : ∀ x, toPlus (toMinus x) = x
  right_inverse : ∀ y, toMinus (toPlus y) = y

def ChiralTwist.equiv {P : ProjectionPair A}
    (τ : ChiralTwist P) : PlusCorner P ≃ MinusCorner P where
  toFun := τ.toMinus
  invFun := τ.toPlus
  left_inv := τ.left_inverse
  right_inv := τ.right_inverse

theorem twist_transport_round_trip
    {P : ProjectionPair A} (τ : ChiralTwist P) (x : PlusCorner P) :
    τ.toPlus (τ.toMinus x) = x :=
  τ.left_inverse x

end InfoGeometry.Clifford.TwistedChiralLinking
