import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring

namespace InfoGeometry.Exceptional.GenericZorn

/-- A 3D vector over a commutative ring R. -/
def Vec3 (R : Type*) := R × R × R

variable {R : Type*} [CommRing R]

def cross (u v : Vec3 R) : Vec3 R :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1,
   u.2.2 * v.1 - u.1 * v.2.2,
   u.1 * v.2.1 - u.2.1 * v.1)

def dot (u v : Vec3 R) : R :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def add (u v : Vec3 R) : Vec3 R :=
  (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2)

def sub (u v : Vec3 R) : Vec3 R :=
  (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2)

def smul (c : R) (u : Vec3 R) : Vec3 R :=
  (c * u.1, c * u.2.1, c * u.2.2)

structure ZornMatrix (R : Type*) where
  a : R
  b : R
  u : Vec3 R
  v : Vec3 R

namespace ZornMatrix

def zero : ZornMatrix R :=
  { a := 0, b := 0, u := (0, 0, 0), v := (0, 0, 0) }

instance : Zero (ZornMatrix R) := ⟨zero⟩

def mul (A B : ZornMatrix R) : ZornMatrix R :=
  { a := A.a * B.a + dot A.u B.v,
    b := A.b * B.b + dot A.v B.u,
    u := sub (add (smul A.a B.u) (smul B.b A.u)) (cross A.v B.v),
    v := add (add (smul B.a A.v) (smul A.b B.v)) (cross A.u B.u) }

instance : Mul (ZornMatrix R) := ⟨mul⟩

@[ext]
lemma ext_lem (A B : ZornMatrix R)
    (ha : A.a = B.a) (hb : A.b = B.b)
    (hu : A.u = B.u) (hv : A.v = B.v) : A = B := by
  cases A
  cases B
  congr

def norm (A : ZornMatrix R) : R :=
  A.a * A.b - dot A.u A.v

theorem norm_mul (A B : ZornMatrix R) : (A * B).norm = A.norm * B.norm := by
  change (A.mul B).norm = A.norm * B.norm
  dsimp [norm, mul, dot, cross, add, sub, smul]
  ring

def trace (A : ZornMatrix R) : R := A.a + A.b

theorem trace_mul_comm (A B : ZornMatrix R) : (A * B).trace = (B * A).trace := by
  change (A.mul B).trace = (B.mul A).trace
  dsimp [trace, mul, dot, cross, add, sub, smul]
  ring

def one : ZornMatrix R :=
  { a := 1, b := 1, u := (0, 0, 0), v := (0, 0, 0) }

instance : One (ZornMatrix R) := ⟨one⟩

def add_mat (A B : ZornMatrix R) : ZornMatrix R :=
  { a := A.a + B.a,
    b := A.b + B.b,
    u := add A.u B.u,
    v := add A.v B.v }

instance : Add (ZornMatrix R) := ⟨add_mat⟩

def neg_mat (A : ZornMatrix R) : ZornMatrix R :=
  { a := -A.a,
    b := -A.b,
    u := smul (-1) A.u,
    v := smul (-1) A.v }

instance : Neg (ZornMatrix R) := ⟨neg_mat⟩

def sub_mat (A B : ZornMatrix R) : ZornMatrix R :=
  { a := A.a - B.a,
    b := A.b - B.b,
    u := sub A.u B.u,
    v := sub A.v B.v }

instance : Sub (ZornMatrix R) := ⟨sub_mat⟩

end ZornMatrix

end InfoGeometry.Exceptional.GenericZorn
