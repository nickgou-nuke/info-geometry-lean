import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic

namespace InfoGeometry.Algebra

universe u
variable (A : Type u) [Ring A] [StarRing A]

/-- 
  The Split Cayley-Dickson Escalation Functor (gamma = +1)
  Constructs the next rank split-algebra A_{n+1} = A_n ⊕ A_n 
-/
structure SplitCD where
  fst : A
  snd : A
  deriving Inhabited

namespace SplitCD
variable {A}

@[simp] def add (x y : SplitCD A) : SplitCD A := ⟨x.fst + y.fst, x.snd + y.snd⟩
@[simp] def neg (x : SplitCD A) : SplitCD A := ⟨-x.fst, -x.snd⟩
@[simp] def zero : SplitCD A := ⟨0, 0⟩

/-- 
  The Split Cayley-Dickson multiplication (* operator)
  (a, b) * (c, d) = (a * c + star d * b, d * a + b * star c) 
-/
@[simp] def mul (x y : SplitCD A) : SplitCD A :=
  ⟨x.fst * y.fst + star y.snd * x.snd,
   y.snd * x.fst + x.snd * star y.fst⟩

/-- The split Cayley-Dickson conjugation -/
@[simp] def star_def (x : SplitCD A) : SplitCD A :=
  ⟨star x.fst, -x.snd⟩

instance : Add (SplitCD A) := ⟨add⟩
instance : Neg (SplitCD A) := ⟨neg⟩
instance : Zero (SplitCD A) := ⟨zero⟩
instance : Mul (SplitCD A) := ⟨mul⟩
instance : Star (SplitCD A) := ⟨star_def⟩

/-- The universal embedding of A into SplitCD A -/
def embed (a : A) : SplitCD A := ⟨a, 0⟩

/-- The J generator (orthogonal split unit) -/
def J : SplitCD A := ⟨0, 1⟩

end SplitCD
end InfoGeometry.Algebra
