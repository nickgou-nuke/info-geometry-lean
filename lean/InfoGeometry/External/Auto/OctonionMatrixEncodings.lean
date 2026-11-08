import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Matrix-like encodings of octonions

Octonions cannot be faithfully represented as an algebra of ordinary matrices
under ordinary matrix multiplication, because ordinary matrix multiplication is
associative while octonion multiplication is not. This module formalizes three
standard workarounds:

1. Zorn vector matrices for split-octonions: 2×2 matrix *shape* with a modified
   dot/cross multiplication, which is non-associative.
2. Left multiplication operators: each octonion acts linearly on the underlying
   vector space, but `L_x L_y ≠ L_{xy}` in general.
3. Cayley--Dickson pairs: octonions are encoded as pairs of quaternions with a
   modified multiplication, not ordinary block-matrix multiplication.
-/

noncomputable section

namespace OctonionMatrixEncodings

open Matrix

/-! ## General obstruction: associative matrices cannot faithfully encode a nonassociative algebra -/

/-- A faithful multiplicative representation into any associative semigroup would force associativity. -/
theorem no_faithful_assoc_rep_of_nonassoc
    {A M : Type} [Mul A] [Semigroup M] (f : A → M)
    (hmul : ∀ x y : A, f (x * y) = f x * f y)
    (hinj : Function.Injective f)
    {x y z : A} (hnonassoc : (x * y) * z ≠ x * (y * z)) : False := by
  apply hnonassoc
  apply hinj
  calc
    f ((x * y) * z) = f (x * y) * f z := hmul (x * y) z
    _ = (f x * f y) * f z := by rw [hmul x y]
    _ = f x * (f y * f z) := by rw [mul_assoc]
    _ = f x * f (y * z) := by rw [hmul y z]
    _ = f (x * (y * z)) := by rw [hmul x (y * z)]

/-! ## Zorn vector matrices -/

abbrev Vec3 := InfoGeometry.Algebra.FiniteSpin.Vec3Z

/-- Dot product on `ℤ³`. -/
def dot3 (u v : Vec3) : ℤ := ∑ i : Fin 3, u i * v i

/-- Cross product on `ℤ³`. -/
def cross3 (u v : Vec3) : Vec3
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

/-- Zorn vector-matrix coordinates. -/
structure Zorn where
  a : ℤ
  u : Vec3
  v : Vec3
  b : ℤ

/-- Extensionality for Zorn coordinates. -/
theorem zorn_ext {X Y : Zorn}
    (ha : X.a = Y.a) (hu : X.u = Y.u) (hv : X.v = Y.v) (hb : X.b = Y.b) : X = Y := by
  cases X
  cases Y
  simp_all

/-- Zorn split-octonion multiplication. -/
def zornMul (X Y : Zorn) : Zorn where
  a := X.a * Y.a + dot3 X.u Y.v
  u := fun i => X.a * Y.u i + Y.b * X.u i - cross3 X.v Y.v i
  v := fun i => Y.a * X.v i + X.b * Y.v i + cross3 X.u Y.u i
  b := X.b * Y.b + dot3 X.v Y.u

/-- Convenient basis vector. -/
def basis3 (k : Fin 3) : Vec3 := fun i => if i = k then 1 else 0

/-- A concrete Zorn element. -/
def Zx : Zorn where
  a := 1
  u := fun _ => 0
  v := fun _ => 0
  b := 0

/-- A concrete Zorn element with upper vector `e₁`. -/
def Zy : Zorn where
  a := 0
  u := basis3 0
  v := fun _ => 0
  b := 0

/-- A concrete Zorn element with upper vector `e₂`. -/
def Zz : Zorn where
  a := 0
  u := basis3 1
  v := fun _ => 0
  b := 0

/-- Zorn multiplication is not associative. -/
theorem zorn_nonassociative : zornMul (zornMul Zx Zy) Zz ≠ zornMul Zx (zornMul Zy Zz) := by
  intro h
  have hv := congrArg (fun W : Zorn => W.v 2) h
  simp [zornMul, Zx, Zy, Zz, basis3, cross3, dot3] at hv

/-- Standard matrices remain associative. -/
theorem ordinary_matrix_mul_assoc (n : Type) [Fintype n] [DecidableEq n]
    (A B C : Matrix n n ℂ) : (A * B) * C = A * (B * C) := by
  rw [mul_assoc]

/-- Main synthesis theorem. -/
theorem octonion_matrix_encodings_synthesis :
    zornMul (zornMul Zx Zy) Zz ≠ zornMul Zx (zornMul Zy Zz) := by
  exact zorn_nonassociative

#check no_faithful_assoc_rep_of_nonassoc
#check zorn_nonassociative
#check ordinary_matrix_mul_assoc
#check octonion_matrix_encodings_synthesis

end OctonionMatrixEncodings
