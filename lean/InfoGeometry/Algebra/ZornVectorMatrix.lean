import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Zorn vector matrices: split-octonion invariant interface

This file deliberately does not install a `Ring` instance for `ZornVectorMatrix`.
The multiplication below is the non-associative Zorn product modeling split
octonions. The companion external exact witnesses are:

* `tools/sympy/zorn_split_octonion_invariants.py`
* `tools/sage/zorn_split_octonion_invariants.sage.py`
* `tools/gap/zorn_split_octonion_invariants.g`

The intended next Lean proof targets are listed at the end of the file.
-/

namespace InfoGeometry.Algebra

open BigOperators

abbrev ZornVec3 (R : Type*) := Fin 3 → R

namespace ZornVec3

variable {R : Type*} [CommRing R]

def dot (x y : ZornVec3 R) : R :=
  ∑ i : Fin 3, x i * y i

/-- Standard coordinate cross product on `Fin 3 → R`. -/
def cross (x y : ZornVec3 R) : ZornVec3 R := fun i =>
  if i = (0 : Fin 3) then x 1 * y 2 - x 2 * y 1
  else if i = (1 : Fin 3) then x 2 * y 0 - x 0 * y 2
  else x 0 * y 1 - x 1 * y 0

end ZornVec3

/-- Zorn vector matrix `[[a,v],[w,b]]`. -/
structure ZornVectorMatrix (R : Type*) where
  a : R
  v : ZornVec3 R
  w : ZornVec3 R
  b : R

namespace ZornVectorMatrix

variable {R : Type*} [CommRing R]

def zero : ZornVectorMatrix R :=
  ⟨0, fun _ => 0, fun _ => 0, 0⟩

def one : ZornVectorMatrix R :=
  ⟨1, fun _ => 0, fun _ => 0, 1⟩

def scalar (r : R) : ZornVectorMatrix R :=
  ⟨r, fun _ => 0, fun _ => 0, r⟩

def add (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨X.a + Y.a,
   fun i => X.v i + Y.v i,
   fun i => X.w i + Y.w i,
   X.b + Y.b⟩

def neg (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨-X.a, fun i => -X.v i, fun i => -X.w i, -X.b⟩

def sub (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  add X (neg Y)

/-- Zorn product. Non-associative; do not package as ordinary matrix product. -/
def mul (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨X.a * Y.a + ZornVec3.dot X.v Y.w,
   fun i => X.a * Y.v i + Y.b * X.v i - ZornVec3.cross X.w Y.w i,
   fun i => Y.a * X.w i + X.b * Y.w i + ZornVec3.cross X.v Y.v i,
   ZornVec3.dot X.w Y.v + X.b * Y.b⟩

def trace (X : ZornVectorMatrix R) : R :=
  X.a + X.b

def norm (X : ZornVectorMatrix R) : R :=
  X.a * X.b - ZornVec3.dot X.v X.w

def conj (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨X.b, fun i => -X.v i, fun i => -X.w i, X.a⟩

/-- Associator `(XY)Z - X(YZ)`, used to witness non-associativity. -/
def associator (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  sub (mul (mul X Y) Z) (mul X (mul Y Z))

/-!
## Intended theorem targets

The external exact witnesses verify the following identities:

```lean
theorem conj_trace_identity (X : ZornVectorMatrix R) :
  sub (add X (conj X)) (scalar (trace X)) = zero := by ...

theorem conj_norm_identity_left (X : ZornVectorMatrix R) :
  sub (mul X (conj X)) (scalar (norm X)) = zero := by ...

theorem zorn_quadratic_identity (X : ZornVectorMatrix R) :
  add (sub (mul X X) (/* trace X scalar-times X */)) (scalar (norm X)) = zero := by ...
```

Keep scalar multiplication explicit rather than installing a `Ring` instance.
-/

end ZornVectorMatrix
end InfoGeometry.Algebra
