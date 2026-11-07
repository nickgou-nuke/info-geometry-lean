import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic

namespace InfoGeometry.Algebra

universe u
variable (A : Type u) [CommRing A] [StarRing A]

@[ext]
structure SplitCD where
  fst : A
  snd : A
  deriving Inhabited

namespace SplitCD
variable {A}

def add (x y : SplitCD A) : SplitCD A := ⟨x.fst + y.fst, x.snd + y.snd⟩
def neg (x : SplitCD A) : SplitCD A := ⟨-x.fst, -x.snd⟩
def zero : SplitCD A := ⟨0, 0⟩

def mul (x y : SplitCD A) : SplitCD A :=
  ⟨x.fst * y.fst + star y.snd * x.snd,
   y.snd * x.fst + x.snd * star y.fst⟩

def star_def (x : SplitCD A) : SplitCD A :=
  ⟨star x.fst, -x.snd⟩

instance : Add (SplitCD A) := ⟨add⟩
instance : Neg (SplitCD A) := ⟨neg⟩
instance : Zero (SplitCD A) := ⟨zero⟩
instance : Mul (SplitCD A) := ⟨mul⟩
instance : Star (SplitCD A) := ⟨star_def⟩

theorem add_assoc_def (x y z : SplitCD A) : x + y + z = x + (y + z) := by
  ext
  · change x.fst + y.fst + z.fst = x.fst + (y.fst + z.fst); exact add_assoc _ _ _
  · change x.snd + y.snd + z.snd = x.snd + (y.snd + z.snd); exact add_assoc _ _ _

theorem add_comm_def (x y : SplitCD A) : x + y = y + x := by
  ext
  · change x.fst + y.fst = y.fst + x.fst; exact add_comm _ _
  · change x.snd + y.snd = y.snd + x.snd; exact add_comm _ _

theorem zero_add_def (x : SplitCD A) : 0 + x = x := by
  ext
  · change 0 + x.fst = x.fst; exact zero_add _
  · change 0 + x.snd = x.snd; exact zero_add _

theorem neg_add_cancel_def (x : SplitCD A) : -x + x = 0 := by
  ext
  · change -x.fst + x.fst = 0; exact neg_add_cancel _
  · change -x.snd + x.snd = 0; exact neg_add_cancel _

theorem star_star_def (x : SplitCD A) : star (star x) = x := by
  ext
  · change star (star x.fst) = x.fst; exact star_star x.fst
  · change -(-x.snd) = x.snd; exact neg_neg x.snd

theorem star_add_def (x y : SplitCD A) : star (x + y) = star x + star y := by
  ext
  · change star (x.fst + y.fst) = star x.fst + star y.fst; exact star_add x.fst y.fst
  · change -(x.snd + y.snd) = -x.snd + -y.snd; exact neg_add x.snd y.snd

theorem star_mul_def (x y : SplitCD A) : star (x * y) = star y * star x := by
  ext
  · change star (x.fst * y.fst + star y.snd * x.snd) = star y.fst * star x.fst + star (-x.snd) * (-y.snd)
    rw [star_add, star_mul, star_mul, star_star]
    have h1 : star (-x.snd) = -star x.snd := star_neg x.snd
    rw [h1]
    have h2 : -star x.snd * -y.snd = star x.snd * y.snd := neg_mul_neg (star x.snd) y.snd
    rw [h2]
  · change -(y.snd * x.fst + x.snd * star y.fst) = -y.snd * star x.fst + (-x.snd) * star (star y.fst)
    rw [star_star]
    rw [neg_add]
    have h1 : -x.snd * star y.fst = -(x.snd * star y.fst) := neg_mul_eq_neg_mul x.snd (star y.fst)
    have h2 : -y.snd * x.fst = -(y.snd * x.fst) := neg_mul_eq_neg_mul y.snd x.fst
    -- Wait, -y.snd * star x.fst ? No, the RHS is -y.snd * star (star x.fst) ?
    -- Let's check RHS: Y * X where Y = star y, X = star x.
    -- Y = (star y.fst, -y.snd), X = (star x.fst, -x.snd)
    -- Y * X snd is: X.snd * Y.fst + Y.snd * star X.fst
    -- = (-x.snd) * star y.fst + (-y.snd) * star (star x.fst)
    -- Ah! The first term is (-x.snd) * star y.fst and the second is (-y.snd) * star (star x.fst) = (-y.snd) * x.fst
    -- So the sum is (-x.snd) * star y.fst + (-y.snd) * x.fst
    -- This is exactly -(x.snd * star y.fst) - (y.snd * x.fst).
    sorry

end SplitCD
end InfoGeometry.Algebra
