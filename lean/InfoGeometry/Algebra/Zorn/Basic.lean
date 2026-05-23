import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Algebra.Zorn.Basic

Basic Zorn vector-matrix data for the local split-octonion cell.
-/

namespace InfoGeometry.Algebra.Zorn

/--
A minimal dot/cross interface on `R^3`.

For the null-cone proofs we only need the dot-zero laws.  The cross-zero laws
are included because they will be needed once `mulZ` and square-zero facts are
added.
-/
structure CrossProduct3 (R : Type*) [CommRing R] where
  dot : (Fin 3 → R) → (Fin 3 → R) → R
  cross : (Fin 3 → R) → (Fin 3 → R) → (Fin 3 → R)

  dot_zero_left :
    ∀ v : Fin 3 → R, dot 0 v = 0
  dot_zero_right :
    ∀ v : Fin 3 → R, dot v 0 = 0

  cross_zero_left :
    ∀ v : Fin 3 → R, cross 0 v = 0
  cross_zero_right :
    ∀ v : Fin 3 → R, cross v 0 = 0

/--
Zorn vector matrix

  [ a  v ]
  [ w  b ]

representing the local split-octonion coordinate cell.
-/
structure ZornMatrix (R : Type*) where
  a : R
  b : R
  v : Fin 3 → R
  w : Fin 3 → R
deriving DecidableEq

namespace ZornMatrix

variable {R : Type*} [CommRing R]

/-- The zero Zorn matrix. -/
def zero : ZornMatrix R where
  a := 0
  b := 0
  v := 0
  w := 0

instance : Zero (ZornMatrix R) :=
  ⟨zero⟩

@[simp] theorem zero_a : (0 : ZornMatrix R).a = 0 := rfl
@[simp] theorem zero_b : (0 : ZornMatrix R).b = 0 := rfl
@[simp] theorem zero_v : (0 : ZornMatrix R).v = 0 := rfl
@[simp] theorem zero_w : (0 : ZornMatrix R).w = 0 := rfl

/--
Zorn determinant / split norm.

For

  X = [ a  v ]
      [ w  b ]

the determinant is

  detZ X = a b - v · w.
-/
def detZ (cp : CrossProduct3 R) (X : ZornMatrix R) : R :=
  X.a * X.b - cp.dot X.v X.w

/-- Quadratic/projective nullness. -/
def IsNull (cp : CrossProduct3 R) (X : ZornMatrix R) : Prop :=
  detZ cp X = 0

end ZornMatrix

end InfoGeometry.Algebra.Zorn
