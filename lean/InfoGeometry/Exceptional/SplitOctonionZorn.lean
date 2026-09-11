import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace InfoGeometry.Exceptional

/-!
# Split Octonions and Zorn Vector Matrix Algebra

The Split Octonions form an 8-dimensional non-associative algebra over the reals.
Unlike the standard octonions (which are a division algebra), the split octonions
contain zero divisors.

A convenient representation of the split octonions is the Zorn Vector Matrix algebra.
Elements are 2x2 matrices where the diagonal elements are scalars (reals) and the
off-diagonal elements are 3D vectors.
-/

/-- A 3D vector over integers. -/
def Vec3 := ℤ × ℤ × ℤ

/-- The cross product of two 3D vectors. -/
def cross (u v : Vec3) : Vec3 :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1,
   u.2.2 * v.1 - u.1 * v.2.2,
   u.1 * v.2.1 - u.2.1 * v.1)

/-- The dot product of two 3D vectors. -/
def dot (u v : Vec3) : ℤ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

/-- Vector addition. -/
def add (u v : Vec3) : Vec3 :=
  (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2)

/-- Vector subtraction. -/
def sub (u v : Vec3) : Vec3 :=
  (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2)

/-- Scalar multiplication. -/
def smul (c : ℤ) (u : Vec3) : Vec3 :=
  (c * u.1, c * u.2.1, c * u.2.2)

/-- 
A Zorn matrix representing an element of the split octonions.
`a` and `b` are scalars.
`u` and `v` are 3D vectors.
-/
structure ZornMatrix where
  a : ℤ
  b : ℤ
  u : Vec3
  v : Vec3

/-- The zero element in the Zorn matrix algebra. -/
def ZornMatrix.zero : ZornMatrix :=
  { a := 0, b := 0, u := (0, 0, 0), v := (0, 0, 0) }

instance : Zero ZornMatrix := ⟨ZornMatrix.zero⟩

/-- 
Multiplication of Zorn matrices. Note this is non-associative.
A * B = [ a*c + u·x,        a*w + d*u - v × x ]
        [ c*v + b*x + u × w, b*d + v·w        ]
-/
def ZornMatrix.mul (A B : ZornMatrix) : ZornMatrix :=
  { a := A.a * B.a + dot A.u B.v,
    b := A.b * B.b + dot A.v B.u,
    u := sub (add (smul A.a B.u) (smul B.b A.u)) (cross A.v B.v),
    v := add (add (smul B.a A.v) (smul A.b B.v)) (cross A.u B.u) }

instance : Mul ZornMatrix := ⟨ZornMatrix.mul⟩

/-- Extensionality lemma for Zorn matrices. -/
lemma ZornMatrix.ext (A B : ZornMatrix)
    (ha : A.a = B.a) (hb : A.b = B.b)
    (hu : A.u = B.u) (hv : A.v = B.v) : A = B := by
  cases A
  cases B
  congr

/-- The split norm of a Zorn matrix: N(A) = a * b - u · v -/
def ZornMatrix.norm (A : ZornMatrix) : ℤ :=
  A.a * A.b - dot A.u A.v

/-!
### Explicit Proof of Zero Divisors

We define two non-zero matrices whose product is exactly zero.
These were derived via the symbolic external solver (SymPy).
-/

def witnessA : ZornMatrix :=
  { a := 1, b := 0, u := (1, 0, 0), v := (0, 0, 0) }

def witnessB : ZornMatrix :=
  { a := 0, b := 1, u := (-1, 0, 0), v := (0, 0, 0) }

theorem split_octonions_have_zero_divisors :
    witnessA * witnessB = 0 ∧ witnessA ≠ 0 ∧ witnessB ≠ 0 := by
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    have h1 : witnessA.a = (0 : ZornMatrix).a := by rw [h]
    change (1 : ℤ) = 0 at h1
    exact one_ne_zero h1
  · intro h
    have h1 : witnessB.b = (0 : ZornMatrix).b := by rw [h]
    change (1 : ℤ) = 0 at h1
    exact one_ne_zero h1

end InfoGeometry.Exceptional
