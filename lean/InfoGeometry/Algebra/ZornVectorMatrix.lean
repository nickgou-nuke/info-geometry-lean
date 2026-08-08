import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.Lie.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

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

def basis (i : Fin 3) : ZornVec3 R :=
  fun j => if j = i then 1 else 0

/-- Coordinate expansion of the dot product on `Fin 3 → R`. -/
theorem dot_eq_sum_coords (x y : ZornVec3 R) :
    dot x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [dot, Fin.sum_univ_three]

/-- Coordinate expansion of the dot product of a vector with itself. -/
theorem dot_self_eq_sum_sq (x : ZornVec3 R) :
    dot x x = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 := by
  rw [dot_eq_sum_coords]

/-- Dot product of coordinate basis vectors. -/
@[simp] theorem dot_basis_basis (i j : Fin 3) :
    dot (basis i : ZornVec3 R) (basis j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [dot, basis]

/-- Dotting a coordinate basis vector on the left reads the matching coordinate. -/
@[simp] theorem dot_basis_left (i : Fin 3) (x : ZornVec3 R) :
    dot (basis i : ZornVec3 R) x = x i := by
  fin_cases i <;> simp [dot, basis]

/-- Dotting a coordinate basis vector on the right reads the matching coordinate. -/
@[simp] theorem dot_basis_right (x : ZornVec3 R) (i : Fin 3) :
    dot x (basis i : ZornVec3 R) = x i := by
  fin_cases i <;> simp [dot, basis]

/-- Equality of all left basis-dot readouts determines a coordinate vector. -/
theorem eq_of_dot_basis_left_eq (x y : ZornVec3 R)
    (h : ∀ i : Fin 3, dot (basis i : ZornVec3 R) x = dot (basis i : ZornVec3 R) y) :
    x = y := by
  ext i
  simpa using h i

/-- Equality of all right basis-dot readouts determines a coordinate vector. -/
theorem eq_of_dot_basis_right_eq (x y : ZornVec3 R)
    (h : ∀ i : Fin 3, dot x (basis i : ZornVec3 R) = dot y (basis i : ZornVec3 R)) :
    x = y := by
  ext i
  simpa using h i

/-- Every coordinate vector is the explicit linear combination of the standard basis. -/
theorem basis_decomposition (x : ZornVec3 R) :
    x =
      fun i =>
        x 0 * basis (0 : Fin 3) i +
          x 1 * basis (1 : Fin 3) i +
            x 2 * basis (2 : Fin 3) i := by
  ext i
  fin_cases i <;> simp [basis]

/-- First coordinate of the coordinate cross product. -/
@[simp] theorem cross_coord_zero (x y : ZornVec3 R) :
    cross x y 0 = x 1 * y 2 - x 2 * y 1 := by
  simp [cross]

/-- Second coordinate of the coordinate cross product. -/
@[simp] theorem cross_coord_one (x y : ZornVec3 R) :
    cross x y 1 = x 2 * y 0 - x 0 * y 2 := by
  simp [cross]

/-- Third coordinate of the coordinate cross product. -/
@[simp] theorem cross_coord_two (x y : ZornVec3 R) :
    cross x y 2 = x 0 * y 1 - x 1 * y 0 := by
  simp [cross]

/-- Coordinate cross product expanded in the standard basis. -/
theorem cross_basis_decomposition (x y : ZornVec3 R) :
    cross x y =
      fun i =>
        (x 1 * y 2 - x 2 * y 1) * basis (0 : Fin 3) i +
          (x 2 * y 0 - x 0 * y 2) * basis (1 : Fin 3) i +
            (x 0 * y 1 - x 1 * y 0) * basis (2 : Fin 3) i := by
  ext i
  fin_cases i <;> simp [cross, basis]

/-- First positive coordinate cross-basis product. -/
@[simp] theorem cross_basis_zero_one :
    cross (basis 0 : ZornVec3 R) (basis 1) = basis 2 := by
  ext i
  fin_cases i <;> simp [cross, basis]

/-- Second positive coordinate cross-basis product. -/
@[simp] theorem cross_basis_one_two :
    cross (basis 1 : ZornVec3 R) (basis 2) = basis 0 := by
  ext i
  fin_cases i <;> simp [cross, basis]

/-- Third positive coordinate cross-basis product. -/
@[simp] theorem cross_basis_two_zero :
    cross (basis 2 : ZornVec3 R) (basis 0) = basis 1 := by
  ext i
  fin_cases i <;> simp [cross, basis]

/-- First negative coordinate cross-basis product. -/
@[simp] theorem cross_basis_one_zero :
    cross (basis 1 : ZornVec3 R) (basis 0) = fun i => -basis 2 i := by
  ext i
  fin_cases i <;> simp [cross, basis]

/-- Second negative coordinate cross-basis product. -/
@[simp] theorem cross_basis_two_one :
    cross (basis 2 : ZornVec3 R) (basis 1) = fun i => -basis 0 i := by
  ext i
  fin_cases i <;> simp [cross, basis]

/-- Third negative coordinate cross-basis product. -/
@[simp] theorem cross_basis_zero_two :
    cross (basis 0 : ZornVec3 R) (basis 2) = fun i => -basis 1 i := by
  ext i
  fin_cases i <;> simp [cross, basis]

/-- Coordinate dot product is symmetric over a commutative ring. -/
theorem dot_comm (x y : ZornVec3 R) :
    dot x y = dot y x := by
  simp [dot, Fin.sum_univ_three, mul_comm]

/-- Coordinate dot product is additive in the left argument. -/
theorem dot_add_left (x y z : ZornVec3 R) :
    dot (x + y) z = dot x z + dot y z := by
  simp [dot, Fin.sum_univ_three]
  ring

/-- Coordinate dot product is additive in the right argument. -/
theorem dot_add_right (x y z : ZornVec3 R) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, Fin.sum_univ_three]
  ring

/-- Coordinate dot product is homogeneous in the left argument. -/
theorem dot_smul_left (r : R) (x y : ZornVec3 R) :
    dot (r • x) y = r * dot x y := by
  simp [dot, Fin.sum_univ_three]
  ring

/-- Coordinate dot product is homogeneous in the right argument. -/
theorem dot_smul_right (r : R) (x y : ZornVec3 R) :
    dot x (r • y) = r * dot x y := by
  simp [dot, Fin.sum_univ_three]
  ring

/-- Coordinate dot product vanishes when the left argument is zero. -/
@[simp] theorem dot_zero_left (x : ZornVec3 R) :
    dot (fun _ => 0) x = 0 := by
  simp [dot]

/-- Coordinate dot product vanishes when the right argument is zero. -/
@[simp] theorem dot_zero_right (x : ZornVec3 R) :
    dot x (fun _ => 0) = 0 := by
  simp [dot]

/-- Coordinate dot product negates in the left argument. -/
theorem dot_neg_left (x y : ZornVec3 R) :
    dot (fun i => -x i) y = -dot x y := by
  simp [dot, Fin.sum_univ_three]

/-- Coordinate dot product negates in the right argument. -/
theorem dot_neg_right (x y : ZornVec3 R) :
    dot x (fun i => -y i) = -dot x y := by
  simp [dot, Fin.sum_univ_three]

/-- Coordinate dot product subtracts in the left argument. -/
theorem dot_sub_left (x y z : ZornVec3 R) :
    dot (x - y) z = dot x z - dot y z := by
  simp [dot, Fin.sum_univ_three]
  ring

/-- Coordinate dot product subtracts in the right argument. -/
theorem dot_sub_right (x y z : ZornVec3 R) :
    dot x (y - z) = dot x y - dot x z := by
  simp [dot, Fin.sum_univ_three]
  ring

/-- Coordinate cross product is antisymmetric. -/
theorem cross_anti (x y : ZornVec3 R) :
    cross y x = fun i => -cross x y i := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- Coordinate cross product is additive in the left argument. -/
theorem cross_add_left (x y z : ZornVec3 R) :
    cross (x + y) z = fun i => cross x z i + cross y z i := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- Coordinate cross product is additive in the right argument. -/
theorem cross_add_right (x y z : ZornVec3 R) :
    cross x (y + z) = fun i => cross x y i + cross x z i := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- Coordinate cross product is homogeneous in the left argument. -/
theorem cross_smul_left (r : R) (x y : ZornVec3 R) :
    cross (r • x) y = fun i => r * cross x y i := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- Coordinate cross product is homogeneous in the right argument. -/
theorem cross_smul_right (r : R) (x y : ZornVec3 R) :
    cross x (r • y) = fun i => r * cross x y i := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- Coordinate cross product vanishes when the left argument is zero. -/
@[simp] theorem cross_zero_left (x : ZornVec3 R) :
    cross (fun _ => 0) x = fun _ => 0 := by
  ext i
  fin_cases i <;> simp [cross]

/-- Coordinate cross product vanishes when the right argument is zero. -/
@[simp] theorem cross_zero_right (x : ZornVec3 R) :
    cross x (fun _ => 0) = fun _ => 0 := by
  ext i
  fin_cases i <;> simp [cross]

/-- Coordinate cross product negates in the left argument. -/
theorem cross_neg_left (x y : ZornVec3 R) :
    cross (fun i => -x i) y = fun i => -cross x y i := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- Coordinate cross product negates in the right argument. -/
theorem cross_neg_right (x y : ZornVec3 R) :
    cross x (fun i => -y i) = fun i => -cross x y i := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- Coordinate cross product subtracts in the left argument. -/
theorem cross_sub_left (x y z : ZornVec3 R) :
    cross (x - y) z = fun i => cross x z i - cross y z i := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- Coordinate cross product subtracts in the right argument. -/
theorem cross_sub_right (x y z : ZornVec3 R) :
    cross x (y - z) = fun i => cross x y i - cross x z i := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- Coordinate cross product of a vector with itself vanishes. -/
@[simp] theorem cross_self (x : ZornVec3 R) :
    cross x x = fun _ => 0 := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- A vector is orthogonal to its coordinate cross product with any other vector. -/
theorem dot_cross_self_left (x y : ZornVec3 R) :
    dot x (cross x y) = 0 := by
  simp [dot, cross, Fin.sum_univ_three]
  ring

/-- The second vector is orthogonal to the coordinate cross product. -/
theorem dot_cross_self_right (x y : ZornVec3 R) :
    dot y (cross x y) = 0 := by
  simp [dot, cross, Fin.sum_univ_three]
  ring

/-- Lagrange identity for the coordinate dot and cross products. -/
theorem dot_cross_cross (x y z w : ZornVec3 R) :
    dot (cross x y) (cross z w) =
      dot x z * dot y w - dot x w * dot y z := by
  simp [dot, cross, Fin.sum_univ_three]
  ring

/-- Square norm form of Lagrange's identity for the coordinate cross product. -/
theorem dot_cross_self (x y : ZornVec3 R) :
    dot (cross x y) (cross x y) = dot x x * dot y y - dot x y * dot x y := by
  rw [dot_cross_cross]
  rw [dot_comm y x]

end ZornVec3

/-- Zorn vector matrix `[[a,v],[w,b]]`. -/
@[ext]
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

/-- First diagonal idempotent. -/
def E11 : ZornVectorMatrix R :=
  ⟨1, fun _ => 0, fun _ => 0, 0⟩

/-- Second diagonal idempotent. -/
def E22 : ZornVectorMatrix R :=
  ⟨0, fun _ => 0, fun _ => 0, 1⟩

/-- Upper off-diagonal basis vector. -/
def U (i : Fin 3) : ZornVectorMatrix R :=
  ⟨0, ZornVec3.basis i, fun _ => 0, 0⟩

/-- Lower off-diagonal basis vector. -/
def V (i : Fin 3) : ZornVectorMatrix R :=
  ⟨0, fun _ => 0, ZornVec3.basis i, 0⟩

/-- Diagonal scalar/lightcone sector of a Zorn vector matrix. -/
def diagonalPart (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨X.a, fun _ => 0, fun _ => 0, X.b⟩

/-- Off-diagonal vector/soldering sector of a Zorn vector matrix. -/
def offDiagonalPart (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨0, X.v, X.w, 0⟩

/-- A pure diagonal Zorn matrix with possibly different diagonal entries. -/
def diagonal (a b : R) : ZornVectorMatrix R :=
  ⟨a, fun _ => 0, fun _ => 0, b⟩

/-- A pure off-diagonal Zorn matrix. -/
def offDiagonal (v w : ZornVec3 R) : ZornVectorMatrix R :=
  ⟨0, v, w, 0⟩

def add (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨X.a + Y.a,
   fun i => X.v i + Y.v i,
   fun i => X.w i + Y.w i,
   X.b + Y.b⟩

def neg (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨-X.a, fun i => -X.v i, fun i => -X.w i, -X.b⟩

def sub (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  add X (neg Y)

def smul (r : R) (X : ZornVectorMatrix R) : ZornVectorMatrix R :=
  ⟨r * X.a, fun i => r * X.v i, fun i => r * X.w i, r * X.b⟩

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

/-- Associator `(XY)Z - X(YZ)`, used to property non-associativity. -/
def associator (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  sub (mul (mul X Y) Z) (mul X (mul Y Z))

/-- Product commutator for the explicit Zorn product. -/
def commutator (X Y : ZornVectorMatrix R) : ZornVectorMatrix R :=
  sub (mul X Y) (mul Y X)

/-- Cyclic Jacobiator of the element commutator. -/
def commutatorJacobiator (X Y Z : ZornVectorMatrix R) : ZornVectorMatrix R :=
  add
    (commutator X (commutator Y Z))
    (add (commutator Y (commutator Z X)) (commutator Z (commutator X Y)))

theorem add_comm (X Y : ZornVectorMatrix R) :
    add X Y = add Y X := by
  ext i <;> simp [add, _root_.add_comm]

theorem add_assoc (X Y Z : ZornVectorMatrix R) :
    add (add X Y) Z = add X (add Y Z) := by
  ext i <;> simp [add, _root_.add_assoc]

theorem add_zero (X : ZornVectorMatrix R) :
    add X zero = X := by
  ext i <;> simp [add, zero]

theorem zero_add (X : ZornVectorMatrix R) :
    add zero X = X := by
  ext i <;> simp [add, zero]

theorem add_left_neg (X : ZornVectorMatrix R) :
    add (neg X) X = zero := by
  ext i <;> simp [add, neg, zero]

@[simp] theorem diagonalPart_add_offDiagonalPart (X : ZornVectorMatrix R) :
    add (diagonalPart X) (offDiagonalPart X) = X := by
  ext i <;> simp [diagonalPart, offDiagonalPart, add]

@[simp] theorem offDiagonalPart_add_diagonalPart (X : ZornVectorMatrix R) :
    add (offDiagonalPart X) (diagonalPart X) = X := by
  ext i <;> simp [diagonalPart, offDiagonalPart, add]

@[simp] theorem diagonalPart_scalar (r : R) :
    diagonalPart (scalar r : ZornVectorMatrix R) = scalar r := by
  ext i <;> simp [diagonalPart, scalar]

@[simp] theorem offDiagonalPart_scalar (r : R) :
    offDiagonalPart (scalar r : ZornVectorMatrix R) = zero := by
  ext i <;> simp [offDiagonalPart, scalar, zero]

@[simp] theorem diagonalPart_offDiagonalPart (X : ZornVectorMatrix R) :
    diagonalPart (offDiagonalPart X) = zero := by
  ext i <;> simp [diagonalPart, offDiagonalPart, zero]

@[simp] theorem offDiagonalPart_diagonalPart (X : ZornVectorMatrix R) :
    offDiagonalPart (diagonalPart X) = zero := by
  ext i <;> simp [diagonalPart, offDiagonalPart, zero]

@[simp] theorem diagonal_eq_diagonalPart (a b : R) :
    diagonalPart (diagonal a b : ZornVectorMatrix R) = diagonal a b := by
  ext i <;> simp [diagonalPart, diagonal]

@[simp] theorem offDiagonal_eq_offDiagonalPart (v w : ZornVec3 R) :
    offDiagonalPart (offDiagonal v w : ZornVectorMatrix R) = offDiagonal v w := by
  ext i <;> simp [offDiagonalPart, offDiagonal]

@[simp] theorem diagonalPart_offDiagonal (v w : ZornVec3 R) :
    diagonalPart (offDiagonal v w : ZornVectorMatrix R) = zero := by
  ext i <;> simp [diagonalPart, offDiagonal, zero]

@[simp] theorem offDiagonalPart_diagonal (a b : R) :
    offDiagonalPart (diagonal a b : ZornVectorMatrix R) = zero := by
  ext i <;> simp [offDiagonalPart, diagonal, zero]

theorem sub_eq_add_neg (X Y : ZornVectorMatrix R) :
    sub X Y = add X (neg Y) :=
  rfl

theorem neg_eq_smul_neg_one (X : ZornVectorMatrix R) :
    neg X = smul (-1 : R) X := by
  ext i <;> simp [neg, smul]

theorem smul_zero (r : R) :
    smul r (zero : ZornVectorMatrix R) = zero := by
  ext i <;> simp [smul, zero]

theorem zero_smul (X : ZornVectorMatrix R) :
    smul (0 : R) X = zero := by
  ext i <;> simp [smul, zero]

theorem one_smul (X : ZornVectorMatrix R) :
    smul (1 : R) X = X := by
  ext i <;> simp [smul]

theorem smul_add (r : R) (X Y : ZornVectorMatrix R) :
    smul r (add X Y) = add (smul r X) (smul r Y) := by
  ext i <;> simp [smul, add, left_distrib]

theorem add_smul (r s : R) (X : ZornVectorMatrix R) :
    smul (r + s) X = add (smul r X) (smul s X) := by
  ext i <;> simp [smul, add, right_distrib]

theorem mul_smul (r : R) (X Y : ZornVectorMatrix R) :
    mul X (smul r Y) = smul r (mul X Y) := by
  ext i
  · simp [mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · simp [mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring

theorem smul_mul (r : R) (X Y : ZornVectorMatrix R) :
    mul (smul r X) Y = smul r (mul X Y) := by
  ext i
  · simp [mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · simp [mul, smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring

theorem mul_zero (X : ZornVectorMatrix R) :
    mul X zero = zero := by
  ext i <;> simp [mul, zero, ZornVec3.dot, ZornVec3.cross]

theorem zero_mul (X : ZornVectorMatrix R) :
    mul zero X = zero := by
  ext i <;> simp [mul, zero, ZornVec3.dot, ZornVec3.cross]

theorem mul_one (X : ZornVectorMatrix R) :
    mul X one = X := by
  ext i <;> simp [mul, one, ZornVec3.dot, ZornVec3.cross]

theorem one_mul (X : ZornVectorMatrix R) :
    mul one X = X := by
  ext i <;> simp [mul, one, ZornVec3.dot, ZornVec3.cross]

theorem scalar_mul (r : R) (X : ZornVectorMatrix R) :
    mul (scalar r) X = smul r X := by
  ext i <;> simp [mul, scalar, smul, ZornVec3.dot, ZornVec3.cross]

theorem mul_scalar (X : ZornVectorMatrix R) (r : R) :
    mul X (scalar r) = smul r X := by
  ext i <;> simp [mul, scalar, smul, ZornVec3.dot, ZornVec3.cross, mul_comm]

theorem scalar_mul_comm (r : R) (X : ZornVectorMatrix R) :
    mul (scalar r) X = mul X (scalar r) := by
  rw [scalar_mul, mul_scalar]

theorem diagonal_mul (a b : R) (X : ZornVectorMatrix R) :
    mul (diagonal a b) X =
      ⟨a * X.a, fun i => a * X.v i, fun i => b * X.w i, b * X.b⟩ := by
  ext i <;> simp [mul, diagonal, ZornVec3.dot, ZornVec3.cross]

theorem mul_diagonal (X : ZornVectorMatrix R) (a b : R) :
    mul X (diagonal a b) =
      ⟨X.a * a, fun i => b * X.v i, fun i => a * X.w i, X.b * b⟩ := by
  ext i <;> simp [mul, diagonal, ZornVec3.dot, ZornVec3.cross]

@[simp] theorem diagonal_mul_diagonal (a b c d : R) :
    mul (diagonal a b : ZornVectorMatrix R) (diagonal c d) =
      diagonal (a * c) (b * d) := by
  ext i <;> simp [mul, diagonal, ZornVec3.dot, ZornVec3.cross]

@[simp] theorem trace_diagonal (a b : R) :
    trace (diagonal a b : ZornVectorMatrix R) = a + b := by
  simp [trace, diagonal]

@[simp] theorem norm_diagonal (a b : R) :
    norm (diagonal a b : ZornVectorMatrix R) = a * b := by
  simp [norm, diagonal, ZornVec3.dot]

theorem trace_diagonal_mul_diagonal (a b c d : R) :
    trace (mul (diagonal a b : ZornVectorMatrix R) (diagonal c d)) =
      a * c + b * d := by
  simp [diagonal_mul_diagonal, trace_diagonal]

theorem norm_diagonal_mul_diagonal (a b c d : R) :
    norm (mul (diagonal a b : ZornVectorMatrix R) (diagonal c d)) =
      norm (diagonal a b : ZornVectorMatrix R) * norm (diagonal c d) := by
  simp [diagonal_mul_diagonal, norm_diagonal]
  ring

/--
Exact obstruction to the false claim that trace is multiplicative on the pure
diagonal section.
-/
theorem trace_diagonal_mul_diagonal_sub_mul_trace (a b c d : R) :
    trace (mul (diagonal a b : ZornVectorMatrix R) (diagonal c d)) -
      trace (diagonal a b : ZornVectorMatrix R) *
        trace (diagonal c d : ZornVectorMatrix R) =
      -(a * d + b * c) := by
  simp [trace_diagonal]
  ring

/--
On the pure diagonal section, trace multiplicativity is equivalent to the
vanishing of the two off-axis scalar products.
-/
theorem trace_diagonal_mul_diagonal_eq_mul_trace_iff (a b c d : R) :
    trace (mul (diagonal a b : ZornVectorMatrix R) (diagonal c d)) =
        trace (diagonal a b : ZornVectorMatrix R) *
          trace (diagonal c d : ZornVectorMatrix R) ↔
      a * d + b * c = 0 := by
  constructor
  · intro htrace
    have hdiff :
        trace (mul (diagonal a b : ZornVectorMatrix R) (diagonal c d)) -
          trace (diagonal a b : ZornVectorMatrix R) *
            trace (diagonal c d : ZornVectorMatrix R) = 0 := by
      rw [htrace]
      ring
    rw [trace_diagonal_mul_diagonal_sub_mul_trace] at hdiff
    exact neg_eq_zero.mp hdiff
  · intro hcross
    apply sub_eq_zero.mp
    rw [trace_diagonal_mul_diagonal_sub_mul_trace, hcross]
    simp

/-- Sufficient form of diagonal trace conservation under the exact scalar constraint. -/
theorem trace_diagonal_mul_diagonal_eq_mul_trace_of_cross_zero
    {a b c d : R} (hcross : a * d + b * c = 0) :
    trace (mul (diagonal a b : ZornVectorMatrix R) (diagonal c d)) =
      trace (diagonal a b : ZornVectorMatrix R) *
        trace (diagonal c d : ZornVectorMatrix R) :=
  (trace_diagonal_mul_diagonal_eq_mul_trace_iff a b c d).mpr hcross

/-- Exact commutator of a pure diagonal and a pure off-diagonal Zorn matrix. -/
theorem commutator_diagonal_offDiagonal (a b : R) (v w : ZornVec3 R) :
    commutator (diagonal a b) (offDiagonal v w) =
      offDiagonal
        (fun i => (a - b) * v i)
        (fun i => (b - a) * w i) := by
  ext i
  · simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot]
  · fin_cases i <;>
      simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.cross] <;>
      ring
  · fin_cases i <;>
      simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.cross] <;>
      ring
  · simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot]

/-- Reversed exact commutator of a pure off-diagonal and a pure diagonal Zorn matrix. -/
theorem commutator_offDiagonal_diagonal (v w : ZornVec3 R) (a b : R) :
    commutator (offDiagonal v w) (diagonal a b) =
      offDiagonal
        (fun i => (b - a) * v i)
        (fun i => (a - b) * w i) := by
  ext i
  · simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot]
  · fin_cases i <;>
      simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.cross] <;>
      ring
  · fin_cases i <;>
      simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.cross] <;>
      ring
  · simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot]

theorem offDiagonal_mul_offDiagonal (v w x y : ZornVec3 R) :
    mul (offDiagonal v w) (offDiagonal x y) =
      add
        (diagonal (ZornVec3.dot v y) (ZornVec3.dot w x))
        (offDiagonal (fun i => -ZornVec3.cross w y i) (ZornVec3.cross v x)) := by
  ext i <;> simp [mul, add, diagonal, offDiagonal]

/-- Exact commutator of two pure off-diagonal Zorn vector matrices. -/
theorem commutator_offDiagonal_offDiagonal (v w x y : ZornVec3 R) :
    commutator (offDiagonal v w) (offDiagonal x y) =
      add
        (diagonal
          (ZornVec3.dot v y - ZornVec3.dot x w)
          (ZornVec3.dot w x - ZornVec3.dot y v))
        (offDiagonal
          (fun i => -(2 : R) * ZornVec3.cross w y i)
          (fun i => (2 : R) * ZornVec3.cross v x i)) := by
  ext i
  · simp [commutator, sub, add, neg, mul, diagonal, offDiagonal]
    ring
  · fin_cases i <;>
      simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.cross] <;>
      ring
  · fin_cases i <;>
      simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.cross] <;>
      ring
  · simp [commutator, sub, add, neg, mul, diagonal, offDiagonal]
    ring

/--
Exact `upper/lower` off-diagonal commutator.  This is the concrete Zorn-vector
statement behind the informal `e+`/`e-` slogan: the commutator has no
off-diagonal component and lands in the diagonal trace-zero sector.
-/
theorem commutator_upper_lower_offDiagonal (v w : ZornVec3 R) :
    commutator (offDiagonal v (fun _ => 0)) (offDiagonal (fun _ => 0) w) =
      diagonal (ZornVec3.dot v w) (-(ZornVec3.dot v w)) := by
  ext i
  · simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot]
  · fin_cases i <;>
      simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.cross]
  · fin_cases i <;>
      simp [commutator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.cross]
  · simp [commutator, sub, add, neg, mul, diagonal, offDiagonal]
    exact ZornVec3.dot_comm w v

/-- The `upper/lower` off-diagonal commutator has zero trace. -/
theorem trace_commutator_upper_lower_offDiagonal (v w : ZornVec3 R) :
    trace (commutator (offDiagonal v (fun _ => 0)) (offDiagonal (fun _ => 0) w)) = 0 := by
  rw [commutator_upper_lower_offDiagonal]
  simp [trace_diagonal]

/-- Basis table for the upper/lower off-diagonal commutator. -/
theorem commutator_U_V (i j : Fin 3) :
    commutator (U i : ZornVectorMatrix R) (V j) =
      diagonal (ZornVec3.basis i j) (-(ZornVec3.basis i j)) := by
  simpa [U, V] using
    (commutator_upper_lower_offDiagonal
      (R := R) (ZornVec3.basis i) (ZornVec3.basis j))

@[simp] theorem commutator_U_V_self (i : Fin 3) :
    commutator (U i : ZornVectorMatrix R) (V i) = diagonal 1 (-1) := by
  simp [commutator_U_V, ZornVec3.basis]

theorem commutator_U_V_of_ne {i j : Fin 3} (hij : i ≠ j) :
    commutator (U i : ZornVectorMatrix R) (V j) = zero := by
  rw [commutator_U_V]
  have hji : j ≠ i := fun h => hij h.symm
  simp [ZornVec3.basis, hji, diagonal, zero]

/-- Reversed basis table for the lower/upper off-diagonal commutator. -/
theorem commutator_V_U (i j : Fin 3) :
    commutator (V i : ZornVectorMatrix R) (U j) =
      diagonal (-(ZornVec3.basis i j)) (ZornVec3.basis i j) := by
  by_cases hij : i = j
  · subst j
    ext k
    · simp [commutator, sub, add, neg, mul, diagonal, U, V, ZornVec3.basis, ZornVec3.dot]
    · fin_cases k <;>
        simp [commutator, sub, add, neg, mul, diagonal, U, V, ZornVec3.cross]
    · fin_cases k <;>
        simp [commutator, sub, add, neg, mul, diagonal, U, V, ZornVec3.cross]
    · simp [commutator, sub, add, neg, mul, diagonal, U, V, ZornVec3.basis, ZornVec3.dot]
  · have hji : j ≠ i := fun h => hij h.symm
    ext k
    · simp [commutator, sub, add, neg, mul, diagonal, U, V, ZornVec3.basis, ZornVec3.dot,
        hij, hji]
    · fin_cases k <;>
        simp [commutator, sub, add, neg, mul, diagonal, U, V, ZornVec3.cross]
    · fin_cases k <;>
        simp [commutator, sub, add, neg, mul, diagonal, U, V, ZornVec3.cross]
    · simp [commutator, sub, add, neg, mul, diagonal, U, V, ZornVec3.basis, ZornVec3.dot,
        hij, hji]

@[simp] theorem commutator_V_U_self (i : Fin 3) :
    commutator (V i : ZornVectorMatrix R) (U i) = diagonal (-1) 1 := by
  simp [commutator_V_U, ZornVec3.basis]

theorem commutator_V_U_of_ne {i j : Fin 3} (hij : i ≠ j) :
    commutator (V i : ZornVectorMatrix R) (U j) = zero := by
  rw [commutator_V_U]
  have hji : j ≠ i := fun h => hij h.symm
  simp [ZornVec3.basis, hji, diagonal, zero]

/-- Basis table for the upper/upper off-diagonal commutator. -/
theorem commutator_U_U (i j : Fin 3) :
    commutator (U i : ZornVectorMatrix R) (U j) =
      offDiagonal (fun _ => 0)
        (fun k => (2 : R) * ZornVec3.cross (ZornVec3.basis i) (ZornVec3.basis j) k) := by
  simpa [U, offDiagonal, diagonal, add] using
    (commutator_offDiagonal_offDiagonal
      (R := R) (ZornVec3.basis i) (fun _ => 0) (ZornVec3.basis j) (fun _ => 0))

@[simp] theorem commutator_U_U_self (i : Fin 3) :
    commutator (U i : ZornVectorMatrix R) (U i) = zero := by
  rw [commutator_U_U]
  ext k <;> simp [offDiagonal, zero, ZornVec3.cross_self]

/-- Basis table for the lower/lower off-diagonal commutator. -/
theorem commutator_V_V (i j : Fin 3) :
    commutator (V i : ZornVectorMatrix R) (V j) =
      offDiagonal
        (fun k => -(2 : R) * ZornVec3.cross (ZornVec3.basis i) (ZornVec3.basis j) k)
        (fun _ => 0) := by
  simpa [V, offDiagonal, diagonal, add] using
    (commutator_offDiagonal_offDiagonal
      (R := R) (fun _ => 0) (ZornVec3.basis i) (fun _ => 0) (ZornVec3.basis j))

@[simp] theorem commutator_V_V_self (i : Fin 3) :
    commutator (V i : ZornVectorMatrix R) (V i) = zero := by
  rw [commutator_V_V]
  ext k <;> simp [offDiagonal, zero, ZornVec3.cross_self]

theorem diagonalPart_offDiagonal_mul_offDiagonal (v w x y : ZornVec3 R) :
    diagonalPart (mul (offDiagonal v w) (offDiagonal x y)) =
      diagonal (ZornVec3.dot v y) (ZornVec3.dot w x) := by
  rw [offDiagonal_mul_offDiagonal]
  ext i <;> simp [diagonalPart, diagonal, offDiagonal, add]

theorem offDiagonalPart_offDiagonal_mul_offDiagonal (v w x y : ZornVec3 R) :
    offDiagonalPart (mul (offDiagonal v w) (offDiagonal x y)) =
      offDiagonal (fun i => -ZornVec3.cross w y i) (ZornVec3.cross v x) := by
  rw [offDiagonal_mul_offDiagonal]
  ext i <;> simp [offDiagonalPart, diagonal, offDiagonal, add]

@[simp] theorem E11_mul_E11 :
    mul (E11 : ZornVectorMatrix R) E11 = E11 := by
  ext i <;> simp [mul, E11, ZornVec3.dot, ZornVec3.cross]

@[simp] theorem E22_mul_E22 :
    mul (E22 : ZornVectorMatrix R) E22 = E22 := by
  ext i <;> simp [mul, E22, ZornVec3.dot, ZornVec3.cross]

@[simp] theorem E11_mul_E22 :
    mul (E11 : ZornVectorMatrix R) E22 = zero := by
  ext i <;> simp [mul, E11, E22, zero, ZornVec3.dot, ZornVec3.cross]

@[simp] theorem E22_mul_E11 :
    mul (E22 : ZornVectorMatrix R) E11 = zero := by
  ext i <;> simp [mul, E11, E22, zero, ZornVec3.dot, ZornVec3.cross]

@[simp] theorem U_mul_self_zero (i : Fin 3) :
    mul (U i : ZornVectorMatrix R) (U i) = zero := by
  fin_cases i
  all_goals
    ext j
    · simp [mul, U, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    · fin_cases j <;> simp [mul, U, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    · fin_cases j <;> simp [mul, U, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    · simp [mul, U, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_mul_self_zero (i : Fin 3) :
    mul (V i : ZornVectorMatrix R) (V i) = zero := by
  fin_cases i
  all_goals
    ext j
    · simp [mul, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    · fin_cases j <;> simp [mul, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    · fin_cases j <;> simp [mul, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    · simp [mul, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_mul_V_self (i : Fin 3) :
    mul (U i : ZornVectorMatrix R) (V i) = E11 := by
  fin_cases i <;>
    ext j <;>
    simp [mul, U, V, E11, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_mul_U_self (i : Fin 3) :
    mul (V i : ZornVectorMatrix R) (U i) = E22 := by
  fin_cases i <;>
    ext j <;>
    simp [mul, U, V, E22, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_zero_mul_U_one :
    mul (U 0 : ZornVectorMatrix R) (U 1) = V 2 := by
  ext j
  · simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_one_mul_U_two :
    mul (U 1 : ZornVectorMatrix R) (U 2) = V 0 := by
  ext j
  · simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_two_mul_U_zero :
    mul (U 2 : ZornVectorMatrix R) (U 0) = V 1 := by
  ext j
  · simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_one_mul_U_zero :
    mul (U 1 : ZornVectorMatrix R) (U 0) = neg (V 2) := by
  ext j
  · simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_two_mul_U_one :
    mul (U 2 : ZornVectorMatrix R) (U 1) = neg (V 0) := by
  ext j
  · simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_zero_mul_U_two :
    mul (U 0 : ZornVectorMatrix R) (U 2) = neg (V 1) := by
  ext j
  · simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_zero_mul_V_one :
    mul (V 0 : ZornVectorMatrix R) (V 1) = neg (U 2) := by
  ext j
  · simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_one_mul_V_two :
    mul (V 1 : ZornVectorMatrix R) (V 2) = neg (U 0) := by
  ext j
  · simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_two_mul_V_zero :
    mul (V 2 : ZornVectorMatrix R) (V 0) = neg (U 1) := by
  ext j
  · simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [mul, U, V, neg, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_one_mul_V_zero :
    mul (V 1 : ZornVectorMatrix R) (V 0) = U 2 := by
  ext j
  · simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_two_mul_V_one :
    mul (V 2 : ZornVectorMatrix R) (V 1) = U 0 := by
  ext j
  · simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_zero_mul_V_two :
    mul (V 0 : ZornVectorMatrix R) (V 2) = U 1 := by
  ext j
  · simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases j <;> simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [mul, U, V, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_zero_mul_V_one :
    mul (U 0 : ZornVectorMatrix R) (V 1) = zero := by
  ext j <;> simp [mul, U, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_zero_mul_V_two :
    mul (U 0 : ZornVectorMatrix R) (V 2) = zero := by
  ext j <;> simp [mul, U, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_one_mul_V_zero :
    mul (U 1 : ZornVectorMatrix R) (V 0) = zero := by
  ext j <;> simp [mul, U, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_one_mul_V_two :
    mul (U 1 : ZornVectorMatrix R) (V 2) = zero := by
  ext j <;> simp [mul, U, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_two_mul_V_zero :
    mul (U 2 : ZornVectorMatrix R) (V 0) = zero := by
  ext j <;> simp [mul, U, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem U_two_mul_V_one :
    mul (U 2 : ZornVectorMatrix R) (V 1) = zero := by
  ext j <;> simp [mul, U, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_zero_mul_U_one :
    mul (V 0 : ZornVectorMatrix R) (U 1) = zero := by
  ext j <;> simp [mul, U, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_zero_mul_U_two :
    mul (V 0 : ZornVectorMatrix R) (U 2) = zero := by
  ext j <;> simp [mul, U, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_one_mul_U_zero :
    mul (V 1 : ZornVectorMatrix R) (U 0) = zero := by
  ext j <;> simp [mul, U, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_one_mul_U_two :
    mul (V 1 : ZornVectorMatrix R) (U 2) = zero := by
  ext j <;> simp [mul, U, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_two_mul_U_zero :
    mul (V 2 : ZornVectorMatrix R) (U 0) = zero := by
  ext j <;> simp [mul, U, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem V_two_mul_U_one :
    mul (V 2 : ZornVectorMatrix R) (U 1) = zero := by
  ext j <;> simp [mul, U, V, zero, ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]

@[simp] theorem associator_scalar_left (r : R) (X Y : ZornVectorMatrix R) :
    associator (scalar r) X Y = zero := by
  unfold associator
  rw [scalar_mul, smul_mul, scalar_mul]
  ext i <;> simp [sub, add, neg, zero]

@[simp] theorem associator_scalar_mid (r : R) (X Y : ZornVectorMatrix R) :
    associator X (scalar r) Y = zero := by
  unfold associator
  rw [mul_scalar, scalar_mul, smul_mul, mul_smul]
  ext i <;> simp [sub, add, neg, zero]

@[simp] theorem associator_scalar_right (r : R) (X Y : ZornVectorMatrix R) :
    associator X Y (scalar r) = zero := by
  unfold associator
  rw [mul_scalar (mul X Y) r, mul_scalar Y r, mul_smul]
  ext i <;> simp [sub, add, neg, zero]

/-- Exact associator obstruction for a pure diagonal element in the left slot. -/
theorem associator_diagonal_left (a b : R) (X Y : ZornVectorMatrix R) :
    associator (diagonal a b) X Y =
      offDiagonal
        (fun i => (a - b) * ZornVec3.cross X.w Y.w i)
        (fun i => (a - b) * ZornVec3.cross X.v Y.v i) := by
  ext i
  · simp [associator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [associator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [associator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · simp [associator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]
    ring

/-- Exact associator obstruction for a pure diagonal element in the middle slot. -/
theorem associator_diagonal_mid (a b : R) (X Y : ZornVectorMatrix R) :
    associator X (diagonal a b) Y =
      offDiagonal
        (fun i => (b - a) * ZornVec3.cross X.w Y.w i)
        (fun i => (b - a) * ZornVec3.cross X.v Y.v i) := by
  ext i
  · simp [associator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [associator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [associator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · simp [associator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]
    ring

/-- Exact associator obstruction for a pure diagonal element in the right slot. -/
theorem associator_diagonal_right (a b : R) (X Y : ZornVectorMatrix R) :
    associator X Y (diagonal a b) =
      offDiagonal
        (fun i => (a - b) * ZornVec3.cross X.w Y.w i)
        (fun i => (a - b) * ZornVec3.cross X.v Y.v i) := by
  ext i
  · simp [associator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [associator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [associator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · simp [associator, sub, add, neg, mul, diagonal, offDiagonal, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]
    ring

@[simp] theorem associator_U_zero_U_one_U_two :
    associator (U 0 : ZornVectorMatrix R) (U 1) (U 2) = sub E22 E11 := by
  unfold associator
  simp

theorem associator_U_zero_U_one_U_two_ne_zero [Nontrivial R] :
    associator (U 0 : ZornVectorMatrix R) (U 1) (U 2) ≠ zero := by
  intro h
  have ha := congrArg ZornVectorMatrix.a h
  simp [associator_U_zero_U_one_U_two, sub, E22, E11, zero, add, neg] at ha

/-- Left alternativity of the explicit Zorn product. -/
theorem associator_left_alternative (X Y : ZornVectorMatrix R) :
    associator X X Y = zero := by
  ext i
  · simp [associator, sub, add, neg, zero, mul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [associator, sub, add, neg, zero, mul, ZornVec3.dot, ZornVec3.cross,
        Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [associator, sub, add, neg, zero, mul, ZornVec3.dot, ZornVec3.cross,
        Fin.sum_univ_three] <;>
      ring
  · simp [associator, sub, add, neg, zero, mul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
    ring

/-- Right alternativity of the explicit Zorn product. -/
theorem associator_right_alternative (X Y : ZornVectorMatrix R) :
    associator X Y Y = zero := by
  ext i
  · simp [associator, sub, add, neg, zero, mul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [associator, sub, add, neg, zero, mul, ZornVec3.dot, ZornVec3.cross,
        Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [associator, sub, add, neg, zero, mul, ZornVec3.dot, ZornVec3.cross,
        Fin.sum_univ_three] <;>
      ring
  · simp [associator, sub, add, neg, zero, mul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
    ring

/-- Flexibility of the explicit Zorn product. -/
theorem associator_flexible (X Y : ZornVectorMatrix R) :
    associator X Y X = zero := by
  ext i
  · simp [associator, sub, add, neg, zero, mul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [associator, sub, add, neg, zero, mul, ZornVec3.dot, ZornVec3.cross,
        Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [associator, sub, add, neg, zero, mul, ZornVec3.dot, ZornVec3.cross,
        Fin.sum_univ_three] <;>
      ring
  · simp [associator, sub, add, neg, zero, mul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three]
    ring

theorem nonassociative_property [Nontrivial R] :
    mul (mul (U 0 : ZornVectorMatrix R) (U 1)) (U 2) ≠
      mul (U 0) (mul (U 1) (U 2)) := by
  intro h
  have ha : (0 : R) = 1 := by
    simpa [mul, U, V, E11, E22, ZornVec3.dot, ZornVec3.cross,
      ZornVec3.basis, Fin.sum_univ_three] using congrArg ZornVectorMatrix.a h
  exact zero_ne_one ha

theorem mul_add (X Y Z : ZornVectorMatrix R) :
    mul X (add Y Z) = add (mul X Y) (mul X Z) := by
  ext i
  · simp [mul, add, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [mul, add, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [mul, add, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · simp [mul, add, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring

theorem add_mul (X Y Z : ZornVectorMatrix R) :
    mul (add X Y) Z = add (mul X Z) (mul Y Z) := by
  ext i
  · simp [mul, add, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [mul, add, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [mul, add, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · simp [mul, add, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    ring

theorem mul_neg (X Y : ZornVectorMatrix R) :
    mul X (neg Y) = neg (mul X Y) := by
  rw [neg_eq_smul_neg_one, mul_smul, ← neg_eq_smul_neg_one]

theorem neg_mul (X Y : ZornVectorMatrix R) :
    mul (neg X) Y = neg (mul X Y) := by
  rw [neg_eq_smul_neg_one, smul_mul, ← neg_eq_smul_neg_one]

theorem mul_sub (X Y Z : ZornVectorMatrix R) :
    mul X (sub Y Z) = sub (mul X Y) (mul X Z) := by
  rw [sub_eq_add_neg, mul_add, mul_neg, sub_eq_add_neg]

theorem sub_mul (X Y Z : ZornVectorMatrix R) :
    mul (sub X Y) Z = sub (mul X Z) (mul Y Z) := by
  rw [sub_eq_add_neg, add_mul, neg_mul, sub_eq_add_neg]

theorem sub_add_sub_cancel_middle
    (A B C D E F : ZornVectorMatrix R) :
    sub (add (add A B) (add C D)) (add (add E C) (add B F)) =
      add (sub A E) (sub D F) := by
  ext i <;> simp [sub, add, neg] <;> ring

@[simp] theorem associator_zero_left (X Y : ZornVectorMatrix R) :
    associator zero X Y = zero := by
  ext i <;>
    simp [associator, mul, zero, sub, add, neg, ZornVec3.dot, ZornVec3.cross]

@[simp] theorem associator_zero_mid (X Y : ZornVectorMatrix R) :
    associator X zero Y = zero := by
  ext i <;>
    simp [associator, mul, zero, sub, add, neg, ZornVec3.dot, ZornVec3.cross]

@[simp] theorem associator_zero_right (X Y : ZornVectorMatrix R) :
    associator X Y zero = zero := by
  ext i <;>
    simp [associator, mul, zero, sub, add, neg, ZornVec3.dot, ZornVec3.cross]

/-- The canonical conjugate has trace part equal to the scalar trace matrix. -/
theorem conj_trace_identity (X : ZornVectorMatrix R) :
    add X (conj X) = scalar (trace X) := by
  ext i <;> simp [add, conj, scalar, trace, _root_.add_comm]

@[simp] theorem trace_zero :
    trace (zero : ZornVectorMatrix R) = 0 := by
  simp [trace, zero]

@[simp] theorem trace_one :
    trace (one : ZornVectorMatrix R) = 2 := by
  simp [trace, one]
  ring

@[simp] theorem trace_scalar (r : R) :
    trace (scalar r : ZornVectorMatrix R) = 2 * r := by
  simp [trace, scalar, two_mul]

@[simp] theorem trace_add (X Y : ZornVectorMatrix R) :
    trace (add X Y) = trace X + trace Y := by
  simp [trace, add]
  ring

@[simp] theorem trace_neg (X : ZornVectorMatrix R) :
    trace (neg X) = -trace X := by
  simp [trace, neg]
  ring

@[simp] theorem trace_sub (X Y : ZornVectorMatrix R) :
    trace (sub X Y) = trace X - trace Y := by
  simp [sub_eq_add_neg]
  ring

@[simp] theorem trace_smul (r : R) (X : ZornVectorMatrix R) :
    trace (smul r X) = r * trace X := by
  simp [trace, smul]
  ring

/-- Conjugation fixes the additive zero. -/
@[simp] theorem conj_zero :
    conj (zero : ZornVectorMatrix R) = zero := by
  ext i <;> simp [conj, zero]

@[simp] theorem conj_conj (X : ZornVectorMatrix R) :
    conj (conj X) = X := by
  ext i <;> simp [conj]

@[simp] theorem conj_add (X Y : ZornVectorMatrix R) :
    conj (add X Y) = add (conj X) (conj Y) := by
  ext i <;> simp [conj, add] <;> ring

@[simp] theorem conj_neg (X : ZornVectorMatrix R) :
    conj (neg X) = neg (conj X) := by
  ext i <;> simp [conj, neg]

@[simp] theorem conj_sub (X Y : ZornVectorMatrix R) :
    conj (sub X Y) = sub (conj X) (conj Y) := by
  simp [sub_eq_add_neg]

@[simp] theorem conj_smul (r : R) (X : ZornVectorMatrix R) :
    conj (smul r X) = smul r (conj X) := by
  ext i <;> simp [conj, smul]

@[simp] theorem trace_conj (X : ZornVectorMatrix R) :
    trace (conj X) = trace X := by
  simp [trace, conj, _root_.add_comm]

@[simp] theorem norm_conj (X : ZornVectorMatrix R) :
    norm (conj X) = norm X := by
  simp [norm, conj, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Zorn conjugation reverses the explicit non-associative product. -/
theorem conj_mul (X Y : ZornVectorMatrix R) :
    conj (mul X Y) = mul (conj Y) (conj X) := by
  ext i
  · simp [conj, mul, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [conj, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [conj, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · simp [conj, mul, ZornVec3.dot, Fin.sum_univ_three]
    ring

/-- Conjugation reverses the associator order and changes its sign. -/
theorem conj_associator (X Y Z : ZornVectorMatrix R) :
    conj (associator X Y Z) = neg (associator (conj Z) (conj Y) (conj X)) := by
  unfold associator
  rw [conj_sub, conj_mul, conj_mul, conj_mul, conj_mul]
  ext i <;> simp [sub, add, neg]

/-- Trace of the explicit Zorn product is symmetric in the two factors. -/
theorem trace_mul_comm (X Y : ZornVectorMatrix R) :
    trace (mul X Y) = trace (mul Y X) := by
  simp [trace, mul, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Trace of the square is controlled by trace and norm. -/
theorem trace_mul_self (X : ZornVectorMatrix R) :
    trace (mul X X) = trace X ^ 2 - (2 : R) * norm X := by
  simp [trace, mul, norm, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  ring

/-- Coordinate discriminant expansion for the trace/norm invariants. -/
theorem trace_sq_sub_four_norm (X : ZornVectorMatrix R) :
    trace X ^ 2 - (4 : R) * norm X =
      (X.a - X.b) ^ 2 + (4 : R) * ZornVec3.dot X.v X.w := by
  simp [trace, norm, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- The associator obstruction has zero scalar trace. -/
theorem trace_associator (X Y Z : ZornVectorMatrix R) :
    trace (associator X Y Z) = 0 := by
  simp [associator, trace, sub, add, neg, mul, ZornVec3.dot, ZornVec3.cross,
    Fin.sum_univ_three]
  ring

@[simp] theorem commutator_self (X : ZornVectorMatrix R) :
    commutator X X = zero := by
  ext i <;> simp [commutator, sub, add, neg, zero]

theorem commutator_skew (X Y : ZornVectorMatrix R) :
    commutator X Y = neg (commutator Y X) := by
  ext i <;> simp [commutator, sub, add, neg]

theorem trace_commutator (X Y : ZornVectorMatrix R) :
    trace (commutator X Y) = 0 := by
  unfold commutator
  simp [trace, sub, add, neg, mul, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- The element-commutator Jacobiator is trace-free, even when it is nonzero. -/
theorem trace_commutatorJacobiator (X Y Z : ZornVectorMatrix R) :
    trace (commutatorJacobiator X Y Z) = 0 := by
  simp [commutatorJacobiator, trace_commutator]

/--
Akivis-style identity for the explicit Zorn product: the Jacobiator of the
commutator is the alternating associator sum.

This is the theorem-honest replacement for any false `LieRing` instance on
Zorn elements.
-/
theorem commutatorJacobiator_eq_associator_alternating
    (X Y Z : ZornVectorMatrix R) :
    commutatorJacobiator X Y Z =
      sub
        (add (add (associator X Z Y) (associator Y X Z)) (associator Z Y X))
        (add (add (associator X Y Z) (associator Y Z X)) (associator Z X Y)) := by
  unfold commutatorJacobiator commutator associator
  repeat rw [mul_sub]
  repeat rw [sub_mul]
  ext i <;> simp [sub, add, neg] <;> abel_nf

/--
Concrete Jacobiator property for the element commutator.

This theorem is intentionally a computation, not a Lie-algebra wrapper: the
Zorn product is non-associative, and its element commutator does not satisfy
Jacobi in characteristics where `6 ≠ 0`.
-/
theorem commutator_jacobi_U_zero_U_one_U_two :
    commutatorJacobiator (U 0 : ZornVectorMatrix R) (U 1) (U 2) =
      diagonal (6 : R) (-6 : R) := by
  ext i
  · simp [commutatorJacobiator, commutator, sub, add, neg, mul, diagonal, U,
      ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    norm_num
  · fin_cases i <;>
      simp [commutatorJacobiator, commutator, sub, add, neg, mul, diagonal, U,
        ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases i <;>
      simp [commutatorJacobiator, commutator, sub, add, neg, mul, diagonal, U,
        ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [commutatorJacobiator, commutator, sub, add, neg, mul, diagonal, U,
      ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    norm_num

/-- In characteristic not dividing `6`, the concrete commutator Jacobiator is nonzero. -/
theorem commutator_jacobi_U_zero_U_one_U_two_ne_zero (h6 : (6 : R) ≠ 0) :
    commutatorJacobiator (U 0 : ZornVectorMatrix R) (U 1) (U 2) ≠
      zero := by
  intro hzero
  have ha := congrArg ZornVectorMatrix.a hzero
  rw [commutator_jacobi_U_zero_U_one_U_two] at ha
  simp [diagonal, zero] at ha
  exact h6 ha

/-- Norm readout of the upper-sector Jacobiator property. -/
theorem norm_commutator_jacobi_U_zero_U_one_U_two :
    norm (commutatorJacobiator (U 0 : ZornVectorMatrix R) (U 1) (U 2)) =
      -(36 : R) := by
  rw [commutator_jacobi_U_zero_U_one_U_two]
  simp [norm_diagonal]
  ring

/-- Lower-sector companion to `commutator_jacobi_U_zero_U_one_U_two`. -/
theorem commutator_jacobi_V_zero_V_one_V_two :
    commutatorJacobiator (V 0 : ZornVectorMatrix R) (V 1) (V 2) =
      diagonal (6 : R) (-6 : R) := by
  ext i
  · simp [commutatorJacobiator, commutator, sub, add, neg, mul, diagonal, V,
      ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    norm_num
  · fin_cases i <;>
      simp [commutatorJacobiator, commutator, sub, add, neg, mul, diagonal, V,
        ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · fin_cases i <;>
      simp [commutatorJacobiator, commutator, sub, add, neg, mul, diagonal, V,
        ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
  · simp [commutatorJacobiator, commutator, sub, add, neg, mul, diagonal, V,
      ZornVec3.dot, ZornVec3.cross, ZornVec3.basis]
    norm_num

/-- In characteristic not dividing `6`, the lower-sector commutator Jacobiator is nonzero. -/
theorem commutator_jacobi_V_zero_V_one_V_two_ne_zero (h6 : (6 : R) ≠ 0) :
    commutatorJacobiator (V 0 : ZornVectorMatrix R) (V 1) (V 2) ≠
      zero := by
  intro hzero
  have ha := congrArg ZornVectorMatrix.a hzero
  rw [commutator_jacobi_V_zero_V_one_V_two] at ha
  simp [diagonal, zero] at ha
  exact h6 ha

/-- Norm readout of the lower-sector Jacobiator property. -/
theorem norm_commutator_jacobi_V_zero_V_one_V_two :
    norm (commutatorJacobiator (V 0 : ZornVectorMatrix R) (V 1) (V 2)) =
      -(36 : R) := by
  rw [commutator_jacobi_V_zero_V_one_V_two]
  simp [norm_diagonal]
  ring

theorem conj_commutator (X Y : ZornVectorMatrix R) :
    conj (commutator X Y) = commutator (conj Y) (conj X) := by
  unfold commutator
  rw [conj_sub, conj_mul, conj_mul]

/-- Conjugation reverses the commutator Jacobiator order and changes its sign. -/
theorem conj_commutatorJacobiator (X Y Z : ZornVectorMatrix R) :
    conj (commutatorJacobiator X Y Z) =
      neg (commutatorJacobiator (conj Z) (conj Y) (conj X)) := by
  unfold commutatorJacobiator
  rw [conj_add, conj_add]
  repeat rw [conj_commutator]
  ext i <;> simp [commutator, sub, add, neg] <;> ring

/-- Exact coordinate formula for the explicit Zorn commutator. -/
theorem commutator_eq (X Y : ZornVectorMatrix R) :
    commutator X Y =
      ⟨ZornVec3.dot X.v Y.w - ZornVec3.dot Y.v X.w,
       fun i =>
        X.a * Y.v i - Y.a * X.v i + Y.b * X.v i - X.b * Y.v i -
          (2 : R) * ZornVec3.cross X.w Y.w i,
       fun i =>
        Y.a * X.w i - X.a * Y.w i + X.b * Y.w i - Y.b * X.w i +
          (2 : R) * ZornVec3.cross X.v Y.v i,
       ZornVec3.dot X.w Y.v - ZornVec3.dot Y.w X.v⟩ := by
  ext i
  · simp [commutator, sub, add, neg, mul]
    ring
  · fin_cases i <;>
      simp [commutator, sub, add, neg, mul, ZornVec3.cross] <;>
      ring
  · fin_cases i <;>
      simp [commutator, sub, add, neg, mul, ZornVec3.cross] <;>
      ring
  · simp [commutator, sub, add, neg, mul]
    ring

@[simp] theorem commutator_scalar_left (r : R) (X : ZornVectorMatrix R) :
    commutator (scalar r) X = zero := by
  unfold commutator
  rw [scalar_mul_comm]
  ext i <;> simp [sub, add, neg, zero]

@[simp] theorem commutator_scalar_right (r : R) (X : ZornVectorMatrix R) :
    commutator X (scalar r) = zero := by
  unfold commutator
  rw [← scalar_mul_comm r X]
  ext i <;> simp [sub, add, neg, zero]

@[simp] theorem commutator_zero_left (X : ZornVectorMatrix R) :
    commutator zero X = zero := by
  unfold commutator
  rw [zero_mul, mul_zero]
  ext i <;> simp [sub, add, neg, zero]

@[simp] theorem commutator_zero_right (X : ZornVectorMatrix R) :
    commutator X zero = zero := by
  unfold commutator
  rw [mul_zero, zero_mul]
  ext i <;> simp [sub, add, neg, zero]

theorem commutator_add_left (X Y Z : ZornVectorMatrix R) :
    commutator (add X Y) Z = add (commutator X Z) (commutator Y Z) := by
  unfold commutator
  rw [add_mul, mul_add]
  ext i <;> simp [sub, add, neg] <;> ring

theorem commutator_add_right (X Y Z : ZornVectorMatrix R) :
    commutator X (add Y Z) = add (commutator X Y) (commutator X Z) := by
  unfold commutator
  rw [mul_add, add_mul]
  ext i <;> simp [sub, add, neg] <;> ring

theorem commutator_smul_left (r : R) (X Y : ZornVectorMatrix R) :
    commutator (smul r X) Y = smul r (commutator X Y) := by
  unfold commutator
  rw [smul_mul, mul_smul]
  ext i <;> simp [sub, add, neg, smul] <;> ring

theorem commutator_smul_right (r : R) (X Y : ZornVectorMatrix R) :
    commutator X (smul r Y) = smul r (commutator X Y) := by
  unfold commutator
  rw [mul_smul, smul_mul]
  ext i <;> simp [sub, add, neg, smul] <;> ring

@[simp] theorem norm_scalar (r : R) :
    norm (scalar r : ZornVectorMatrix R) = r * r := by
  simp [norm, scalar, ZornVec3.dot]

@[simp] theorem norm_zero :
    norm (zero : ZornVectorMatrix R) = 0 := by
  simp [norm, zero, ZornVec3.dot]

@[simp] theorem norm_one :
    norm (one : ZornVectorMatrix R) = 1 := by
  simp [norm, one, ZornVec3.dot]

@[simp] theorem norm_smul (r : R) (X : ZornVectorMatrix R) :
    norm (smul r X) = r ^ 2 * norm X := by
  simp [norm, smul, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- The explicit Zorn quadratic norm is even under additive negation. -/
@[simp] theorem norm_neg (X : ZornVectorMatrix R) :
    norm (neg X) = norm X := by
  simp [norm, neg, ZornVec3.dot, Fin.sum_univ_three]

/-- Direct polarization expansion for the explicit Zorn quadratic norm. -/
theorem norm_add (X Y : ZornVectorMatrix R) :
    norm (add X Y) =
      norm X + norm Y + X.a * Y.b + Y.a * X.b -
        (ZornVec3.dot X.v Y.w + ZornVec3.dot Y.v X.w) := by
  simp [norm, add, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Direct expansion of the norm of an additive difference. -/
theorem norm_sub (X Y : ZornVectorMatrix R) :
    norm (sub X Y) =
      norm X + norm Y - X.a * Y.b - Y.a * X.b +
        (ZornVec3.dot X.v Y.w + ZornVec3.dot Y.v X.w) := by
  simp [sub, add, neg, norm, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Parallelogram identity for the explicit Zorn quadratic norm. -/
theorem norm_add_add_norm_sub (X Y : ZornVectorMatrix R) :
    norm (add X Y) + norm (sub X Y) = (2 : R) * (norm X + norm Y) := by
  rw [norm_add, norm_sub]
  ring

/-- Polarization difference for the explicit Zorn quadratic norm. -/
theorem norm_add_sub_norm_sub (X Y : ZornVectorMatrix R) :
    norm (add X Y) - norm (sub X Y) =
      (2 : R) *
        (X.a * Y.b + Y.a * X.b -
          (ZornVec3.dot X.v Y.w + ZornVec3.dot Y.v X.w)) := by
  rw [norm_add, norm_sub]
  ring

/-- Scalar multiplication preserves the null cone. -/
theorem norm_smul_eq_zero_of_norm_eq_zero (r : R) (X : ZornVectorMatrix R)
    (hX : norm X = 0) :
    norm (smul r X) = 0 := by
  rw [norm_smul, hX]
  simp

/-- Over a field, nonzero scalar multiplication preserves non-isotropic elements. -/
theorem norm_smul_ne_zero {K : Type*} [Field K]
    (r : K) (X : ZornVectorMatrix K) (hr : r ≠ 0) (hX : norm X ≠ 0) :
    norm (smul r X) ≠ 0 := by
  rw [norm_smul]
  exact mul_ne_zero (pow_ne_zero 2 hr) hX

/-- Over a field, nonzero scalar multiplication preserves and reflects nullness. -/
theorem norm_smul_eq_zero_iff {K : Type*} [Field K]
    (r : K) (X : ZornVectorMatrix K) (hr : r ≠ 0) :
    norm (smul r X) = 0 ↔ norm X = 0 := by
  rw [norm_smul]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hr)
  · intro h
    rw [h]
    simp

@[simp] theorem norm_diagonalPart (X : ZornVectorMatrix R) :
    norm (diagonalPart X) = X.a * X.b := by
  simp [norm, diagonalPart, ZornVec3.dot]

@[simp] theorem norm_offDiagonalPart (X : ZornVectorMatrix R) :
    norm (offDiagonalPart X) = -ZornVec3.dot X.v X.w := by
  simp [norm, offDiagonalPart]

/-- Right multiplication by the conjugate collapses to the scalar norm matrix. -/
theorem conj_norm_identity_left (X : ZornVectorMatrix R) :
    mul X (conj X) = scalar (norm X) := by
  ext i
  · simp [mul, conj, scalar, norm, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [mul, conj, scalar, norm, ZornVec3.cross] <;>
      ring
  · fin_cases i <;>
      simp [mul, conj, scalar, norm, ZornVec3.cross] <;>
      ring
  · simp [mul, conj, scalar, norm, ZornVec3.dot, Fin.sum_univ_three]
    ring

/-- Left multiplication by the conjugate also collapses to the scalar norm matrix. -/
theorem conj_norm_identity_right (X : ZornVectorMatrix R) :
    mul (conj X) X = scalar (norm X) := by
  ext i
  · simp [mul, conj, scalar, norm, ZornVec3.dot, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [mul, conj, scalar, norm, ZornVec3.cross] <;>
      ring
  · fin_cases i <;>
      simp [mul, conj, scalar, norm, ZornVec3.cross] <;>
      ring
  · simp [mul, conj, scalar, norm, ZornVec3.dot, Fin.sum_univ_three]
    ring

/-- The Zorn quadratic norm is multiplicative for the explicit coordinate product. -/
theorem norm_mul (X Y : ZornVectorMatrix R) :
    norm (mul X Y) = norm X * norm Y := by
  simp [norm, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  ring

/-- Quadratic characteristic equation for the explicit Zorn vector matrix. -/
theorem characteristic_equation (X : ZornVectorMatrix R) :
    add (sub (mul X X) (smul (trace X) X)) (scalar (norm X)) = zero := by
  ext i
  · simp [mul, sub, add, neg, smul, scalar, trace, norm, zero, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]
    ring
  · fin_cases i <;>
      simp [mul, sub, add, neg, smul, scalar, trace, norm, zero, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · fin_cases i <;>
      simp [mul, sub, add, neg, smul, scalar, trace, norm, zero, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three] <;>
      ring
  · simp [mul, sub, add, neg, smul, scalar, trace, norm, zero, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three]
    ring

/-- Norm expansion for `1 - tX`, the Zorn analogue of a finite Fredholm polynomial. -/
theorem norm_one_sub_smul (t : R) (X : ZornVectorMatrix R) :
    norm (sub one (smul t X)) = 1 - t * trace X + t ^ 2 * norm X := by
  simp [norm, sub, add, neg, one, smul, trace, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Characteristic norm polynomial for a scalar minus an explicit Zorn vector matrix. -/
theorem norm_scalar_sub (t : R) (X : ZornVectorMatrix R) :
    norm (sub (scalar t) X) = t ^ 2 - t * trace X + norm X := by
  simp [norm, sub, add, neg, scalar, trace, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- The same characteristic norm polynomial for an explicit Zorn vector matrix minus a scalar. -/
theorem norm_sub_scalar (X : ZornVectorMatrix R) (t : R) :
    norm (sub X (scalar t)) = t ^ 2 - t * trace X + norm X := by
  simp [norm, sub, add, neg, scalar, trace, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Adjugate divided by the norm on the non-isotropic locus. -/
def inverseCandidate {K : Type*} [Field K] (X : ZornVectorMatrix K) : ZornVectorMatrix K :=
  smul (norm X)⁻¹ (conj X)

/-- Scaling the scalar norm matrix by the inverse norm gives the identity. -/
theorem smul_scalar_inv_norm {K : Type*} [Field K]
    (X : ZornVectorMatrix K) (hX : norm X ≠ 0) :
    smul (norm X)⁻¹ (scalar (norm X)) = one := by
  ext i
  · simp [smul, scalar, one, hX]
  · simp [smul, scalar, one]
  · simp [smul, scalar, one]
  · simp [smul, scalar, one, hX]

/-- A non-isotropic Zorn vector matrix has a right inverse given by its conjugate over the norm. -/
theorem mul_inverseCandidate {K : Type*} [Field K]
    (X : ZornVectorMatrix K) (hX : norm X ≠ 0) :
    mul X (inverseCandidate X) = one := by
  unfold inverseCandidate
  rw [mul_smul, conj_norm_identity_left]
  exact smul_scalar_inv_norm X hX

/-- A non-isotropic Zorn vector matrix has a left inverse given by its conjugate over the norm. -/
theorem inverseCandidate_mul {K : Type*} [Field K]
    (X : ZornVectorMatrix K) (hX : norm X ≠ 0) :
    mul (inverseCandidate X) X = one := by
  unfold inverseCandidate
  rw [smul_mul, conj_norm_identity_right]
  exact smul_scalar_inv_norm X hX

/-- Paired inverse-candidate packet on the non-isotropic norm locus. -/
theorem inverseCandidate_packet {K : Type*} [Field K]
    (X : ZornVectorMatrix K) (hX : norm X ≠ 0) :
    mul X (inverseCandidate X) = one ∧ mul (inverseCandidate X) X = one := by
  exact ⟨mul_inverseCandidate X hX, inverseCandidate_mul X hX⟩

/-- The non-isotropic norm locus is closed under the Zorn product. -/
theorem norm_mul_ne_zero {K : Type*} [Field K]
    (X Y : ZornVectorMatrix K) (hX : norm X ≠ 0) (hY : norm Y ≠ 0) :
    norm (mul X Y) ≠ 0 := by
  rw [norm_mul]
  exact mul_ne_zero hX hY

/-- The inverse candidate has reciprocal norm. -/
theorem norm_inverseCandidate {K : Type*} [Field K]
    (X : ZornVectorMatrix K) :
    norm (inverseCandidate X) = (norm X)⁻¹ ^ 2 * norm X := by
  unfold inverseCandidate
  rw [← mul_scalar, norm_mul, norm_scalar, norm_conj]
  ring

/-- On the non-isotropic locus, the inverse candidate has norm `(norm X)⁻¹`. -/
theorem norm_inverseCandidate_of_ne_zero {K : Type*} [Field K]
    (X : ZornVectorMatrix K) (hX : norm X ≠ 0) :
    norm (inverseCandidate X) = (norm X)⁻¹ := by
  rw [norm_inverseCandidate]
  field_simp [hX]

/-- The inverse candidate of a non-isotropic element is again non-isotropic. -/
theorem norm_inverseCandidate_ne_zero {K : Type*} [Field K]
    (X : ZornVectorMatrix K) (hX : norm X ≠ 0) :
    norm (inverseCandidate X) ≠ 0 := by
  rw [norm_inverseCandidate_of_ne_zero X hX]
  exact inv_ne_zero hX

/-- Trace of the inverse candidate is the trace scaled by the reciprocal norm. -/
theorem trace_inverseCandidate {K : Type*} [Field K]
    (X : ZornVectorMatrix K) :
    trace (inverseCandidate X) = (norm X)⁻¹ * trace X := by
  unfold inverseCandidate
  simp

/-- Taking the inverse candidate twice returns the original non-isotropic element. -/
theorem inverseCandidate_inverseCandidate {K : Type*} [Field K]
    (X : ZornVectorMatrix K) (hX : norm X ≠ 0) :
    inverseCandidate (inverseCandidate X) = X := by
  change smul (norm (inverseCandidate X))⁻¹ (conj (inverseCandidate X)) = X
  rw [norm_inverseCandidate_of_ne_zero X hX]
  unfold inverseCandidate
  rw [conj_smul, conj_conj]
  ext i <;> simp [smul, hX]

/--
An explicit derivation of the non-associative Zorn product.

The structure is intentionally stated against the local operations `add`,
`smul`, and `mul`, rather than using a `Ring` or `Module` instance.  This keeps
the non-associative algebra surface theorem-honest.
-/
structure Derivation where
  toFun : ZornVectorMatrix R → ZornVectorMatrix R
  map_add' : ∀ X Y, toFun (add X Y) = add (toFun X) (toFun Y)
  map_smul' : ∀ (r : R) X, toFun (smul r X) = smul r (toFun X)
  map_mul' : ∀ X Y, toFun (mul X Y) = add (mul (toFun X) Y) (mul X (toFun Y))

namespace Derivation

instance : CoeFun (Derivation (R := R)) (fun _ => ZornVectorMatrix R → ZornVectorMatrix R) where
  coe D := D.toFun

theorem ext {D E : Derivation (R := R)} (h : ∀ X, D X = E X) : D = E := by
  cases D
  cases E
  simp only at h
  congr
  exact funext h

@[simp] theorem map_add (D : Derivation (R := R)) (X Y : ZornVectorMatrix R) :
    D (add X Y) = add (D X) (D Y) :=
  D.map_add' X Y

@[simp] theorem map_smul (D : Derivation (R := R)) (r : R) (X : ZornVectorMatrix R) :
    D (smul r X) = smul r (D X) :=
  D.map_smul' r X

@[simp] theorem map_mul (D : Derivation (R := R)) (X Y : ZornVectorMatrix R) :
    D (mul X Y) = add (mul (D X) Y) (mul X (D Y)) :=
  D.map_mul' X Y

@[simp] theorem map_zero (D : Derivation (R := R)) :
    D ZornVectorMatrix.zero = ZornVectorMatrix.zero := by
  calc
    D ZornVectorMatrix.zero = D (ZornVectorMatrix.smul (0 : R) ZornVectorMatrix.zero) := by
      rw [zero_smul]
    _ = ZornVectorMatrix.smul (0 : R) (D ZornVectorMatrix.zero) := D.map_smul' 0 ZornVectorMatrix.zero
    _ = ZornVectorMatrix.zero := zero_smul _

@[simp] theorem map_neg (D : Derivation (R := R)) (X : ZornVectorMatrix R) :
    D (ZornVectorMatrix.neg X) = ZornVectorMatrix.neg (D X) := by
  rw [neg_eq_smul_neg_one, D.map_smul', ← neg_eq_smul_neg_one]

@[simp] theorem map_sub (D : Derivation (R := R)) (X Y : ZornVectorMatrix R) :
    D (sub X Y) = sub (D X) (D Y) := by
  simp [sub_eq_add_neg]

@[simp] theorem map_one (D : Derivation (R := R)) :
    D one = zero := by
  have h := D.map_mul' one one
  simp [mul_one, one_mul] at h
  ext i
  · have ha := congrArg ZornVectorMatrix.a h
    simp [ZornVectorMatrix.add] at ha
    have hcancel : (0 : R) = (D one).a :=
      add_left_cancel (a := (D one).a) (b := 0) (c := (D one).a) (by simpa using ha)
    exact hcancel.symm
  · have hv := congrArg (fun X : ZornVectorMatrix R => X.v i) h
    simp [ZornVectorMatrix.add] at hv
    have hcancel : (0 : R) = (D one).v i :=
      add_left_cancel (a := (D one).v i) (b := 0) (c := (D one).v i) (by simpa using hv)
    exact hcancel.symm
  · have hw := congrArg (fun X : ZornVectorMatrix R => X.w i) h
    simp [ZornVectorMatrix.add] at hw
    have hcancel : (0 : R) = (D one).w i :=
      add_left_cancel (a := (D one).w i) (b := 0) (c := (D one).w i) (by simpa using hw)
    exact hcancel.symm
  · have hb := congrArg ZornVectorMatrix.b h
    simp [ZornVectorMatrix.add] at hb
    have hcancel : (0 : R) = (D one).b :=
      add_left_cancel (a := (D one).b) (b := 0) (c := (D one).b) (by simpa using hb)
    exact hcancel.symm

@[simp] theorem map_scalar (D : Derivation (R := R)) (r : R) :
    D (scalar r) = zero := by
  have hscalar : scalar r = smul r one := by
    ext i <;> simp [scalar, smul, one]
  rw [hscalar, D.map_smul', D.map_one, ZornVectorMatrix.smul_zero]

theorem map_conj_eq_neg (D : Derivation (R := R)) (X : ZornVectorMatrix R) :
    D (conj X) = ZornVectorMatrix.neg (D X) := by
  have h := congrArg D (conj_trace_identity X)
  rw [D.map_add', D.map_scalar] at h
  ext i
  · have ha := congrArg ZornVectorMatrix.a h
    simp [ZornVectorMatrix.add, ZornVectorMatrix.zero] at ha
    exact eq_neg_of_add_eq_zero_left (by simpa [_root_.add_comm] using ha)
  · have hv := congrArg (fun Y : ZornVectorMatrix R => Y.v i) h
    simp [ZornVectorMatrix.add, ZornVectorMatrix.zero] at hv
    exact eq_neg_of_add_eq_zero_left (by simpa [_root_.add_comm] using hv)
  · have hw := congrArg (fun Y : ZornVectorMatrix R => Y.w i) h
    simp [ZornVectorMatrix.add, ZornVectorMatrix.zero] at hw
    exact eq_neg_of_add_eq_zero_left (by simpa [_root_.add_comm] using hw)
  · have hb := congrArg ZornVectorMatrix.b h
    simp [ZornVectorMatrix.add, ZornVectorMatrix.zero] at hb
    exact eq_neg_of_add_eq_zero_left (by simpa [_root_.add_comm] using hb)

theorem derivation_conj_norm_identity_left
    (D : Derivation (R := R)) (X : ZornVectorMatrix R) :
    add (mul (D X) (conj X)) (mul X (D (conj X))) = zero := by
  have h := congrArg D (conj_norm_identity_left X)
  rw [D.map_mul', D.map_scalar] at h
  exact h

theorem derivation_conj_norm_identity_right
    (D : Derivation (R := R)) (X : ZornVectorMatrix R) :
    add (mul (D (conj X)) X) (mul (conj X) (D X)) = zero := by
  have h := congrArg D (conj_norm_identity_right X)
  rw [D.map_mul', D.map_scalar] at h
  exact h

/-- The zero map is a derivation. -/
def zero : Derivation (R := R) where
  toFun := fun _ => ZornVectorMatrix.zero
  map_add' := by
    intro X Y
    ext i <;> simp [ZornVectorMatrix.add, ZornVectorMatrix.zero]
  map_smul' := by
    intro r X
    ext i <;> simp [ZornVectorMatrix.smul, ZornVectorMatrix.zero]
  map_mul' := by
    intro X Y
    ext i <;>
      simp [ZornVectorMatrix.add, ZornVectorMatrix.zero, mul, ZornVec3.dot,
        ZornVec3.cross]

/-- Pointwise sum of two derivations. -/
def add (D E : Derivation (R := R)) : Derivation (R := R) where
  toFun := fun X => ZornVectorMatrix.add (D X) (E X)
  map_add' := by
    intro X Y
    rw [D.map_add', E.map_add']
    ext i <;> simp [ZornVectorMatrix.add] <;> ring
  map_smul' := by
    intro r X
    rw [D.map_smul', E.map_smul']
    ext i <;> simp [ZornVectorMatrix.add, ZornVectorMatrix.smul] <;> ring
  map_mul' := by
    intro X Y
    rw [D.map_mul', E.map_mul']
    ext i
    · simp [ZornVectorMatrix.add, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring
    · fin_cases i <;>
        simp [ZornVectorMatrix.add, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
        ring
    · fin_cases i <;>
        simp [ZornVectorMatrix.add, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;>
        ring
    · simp [ZornVectorMatrix.add, mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
      ring

@[simp] theorem zero_apply (X : ZornVectorMatrix R) :
    (zero (R := R)) X = ZornVectorMatrix.zero :=
  rfl

@[simp] theorem add_apply (D E : Derivation (R := R)) (X : ZornVectorMatrix R) :
    (add D E) X = ZornVectorMatrix.add (D X) (E X) :=
  rfl

/-- Pointwise negation of a derivation. -/
def neg (D : Derivation (R := R)) : Derivation (R := R) where
  toFun := fun X => ZornVectorMatrix.neg (D X)
  map_add' := by
    intro X Y
    rw [D.map_add']
    ext i <;> simp [ZornVectorMatrix.add, ZornVectorMatrix.neg] <;> ring
  map_smul' := by
    intro r X
    rw [D.map_smul']
    ext i <;> simp [smul, ZornVectorMatrix.neg]
  map_mul' := by
    intro X Y
    rw [D.map_mul']
    ext i
    · simp [ZornVectorMatrix.add, ZornVectorMatrix.neg, mul, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three]
      ring
    · fin_cases i <;>
        simp [ZornVectorMatrix.add, ZornVectorMatrix.neg, mul, ZornVec3.dot,
          ZornVec3.cross, Fin.sum_univ_three] <;>
        ring
    · fin_cases i <;>
        simp [ZornVectorMatrix.add, ZornVectorMatrix.neg, mul, ZornVec3.dot,
          ZornVec3.cross, Fin.sum_univ_three] <;>
        ring
    · simp [ZornVectorMatrix.add, ZornVectorMatrix.neg, mul, ZornVec3.dot,
        ZornVec3.cross, Fin.sum_univ_three]
      ring

@[simp] theorem neg_apply (D : Derivation (R := R)) (X : ZornVectorMatrix R) :
    (neg D) X = ZornVectorMatrix.neg (D X) :=
  rfl

/-- Scalar multiple of a derivation. -/
def smul (r : R) (D : Derivation (R := R)) : Derivation (R := R) where
  toFun := fun X => ZornVectorMatrix.smul r (D X)
  map_add' := by
    intro X Y
    rw [D.map_add', smul_add]
  map_smul' := by
    intro s X
    rw [D.map_smul']
    ext i <;> simp [ZornVectorMatrix.smul] <;> ring
  map_mul' := by
    intro X Y
    rw [D.map_mul', smul_add, smul_mul, mul_smul]

@[simp] theorem smul_apply (r : R) (D : Derivation (R := R)) (X : ZornVectorMatrix R) :
    (smul r D) X = ZornVectorMatrix.smul r (D X) :=
  rfl

/-- Pointwise difference of two derivations. -/
def sub (D E : Derivation (R := R)) : Derivation (R := R) :=
  add D (neg E)

@[simp] theorem sub_apply (D E : Derivation (R := R)) (X : ZornVectorMatrix R) :
    (sub D E) X = ZornVectorMatrix.sub (D X) (E X) :=
  rfl

theorem add_comm (D E : Derivation (R := R)) :
    add D E = add E D := by
  apply ext
  intro X
  ext i <;> simp [add, ZornVectorMatrix.add] <;> ring

theorem add_assoc (D E F : Derivation (R := R)) :
    add (add D E) F = add D (add E F) := by
  apply ext
  intro X
  ext i <;> simp [add, ZornVectorMatrix.add] <;> ring

theorem add_zero (D : Derivation (R := R)) :
    add D zero = D := by
  apply ext
  intro X
  ext i <;> simp [add, zero, ZornVectorMatrix.add, ZornVectorMatrix.zero]

theorem zero_add (D : Derivation (R := R)) :
    add zero D = D := by
  apply ext
  intro X
  ext i <;> simp [add, zero, ZornVectorMatrix.add, ZornVectorMatrix.zero]

theorem add_left_neg (D : Derivation (R := R)) :
    add (neg D) D = zero := by
  apply ext
  intro X
  ext i <;> simp [add, neg, zero, ZornVectorMatrix.add, ZornVectorMatrix.neg,
    ZornVectorMatrix.zero]

theorem sub_eq_add_neg (D E : Derivation (R := R)) :
    sub D E = add D (neg E) :=
  rfl

theorem smul_zero (r : R) :
    smul r (zero (R := R)) = zero := by
  apply ext
  intro X
  ext i <;> simp [smul, zero, ZornVectorMatrix.smul, ZornVectorMatrix.zero]

theorem zero_smul (D : Derivation (R := R)) :
    smul (0 : R) D = zero := by
  apply ext
  intro X
  ext i <;> simp [smul, zero, ZornVectorMatrix.smul, ZornVectorMatrix.zero]

theorem one_smul (D : Derivation (R := R)) :
    smul (1 : R) D = D := by
  apply ext
  intro X
  ext i <;> simp [smul, ZornVectorMatrix.smul]

theorem smul_add (r : R) (D E : Derivation (R := R)) :
    smul r (add D E) = add (smul r D) (smul r E) := by
  apply ext
  intro X
  ext i <;> simp [smul, add, ZornVectorMatrix.smul, ZornVectorMatrix.add] <;> ring

theorem add_smul (r s : R) (D : Derivation (R := R)) :
    smul (r + s) D = add (smul r D) (smul s D) := by
  apply ext
  intro X
  ext i <;> simp [smul, add, ZornVectorMatrix.smul, ZornVectorMatrix.add] <;> ring

theorem smul_smul (r s : R) (D : Derivation (R := R)) :
    smul r (smul s D) = smul (r * s) D := by
  apply ext
  intro X
  ext i <;> simp [smul, ZornVectorMatrix.smul] <;> ring

@[simp] theorem neg_eq_smul_neg_one (D : Derivation (R := R)) :
    neg D = smul (-1 : R) D := by
  apply ext
  intro X
  ext i <;> simp [neg, smul, ZornVectorMatrix.neg_eq_smul_neg_one]

/-- Commutator bracket of derivations. -/
def bracket (D E : Derivation (R := R)) : Derivation (R := R) where
  toFun := fun X => ZornVectorMatrix.sub (D (E X)) (E (D X))
  map_add' := by
    intro X Y
    rw [E.map_add', D.map_add', D.map_add', E.map_add']
    ext i <;> simp [ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg] <;> ring
  map_smul' := by
    intro r X
    rw [E.map_smul', D.map_smul', D.map_smul', E.map_smul']
    ext i <;>
      simp [ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg,
        ZornVectorMatrix.smul] <;>
      ring
  map_mul' := by
    intro X Y
    simp only [map_mul, map_add, sub_mul, mul_sub]
    exact sub_add_sub_cancel_middle
      (mul (D (E X)) Y)
      (mul (E X) (D Y))
      (mul (D X) (E Y))
      (mul X (D (E Y)))
      (mul (E (D X)) Y)
      (mul X (E (D Y)))

@[simp] theorem bracket_apply (D E : Derivation (R := R)) (X : ZornVectorMatrix R) :
    (bracket D E) X = ZornVectorMatrix.sub (D (E X)) (E (D X)) :=
  rfl

@[simp] theorem bracket_self (D : Derivation (R := R)) :
    bracket D D = zero := by
  apply ext
  intro X
  ext i <;> simp [bracket, zero, ZornVectorMatrix.sub, ZornVectorMatrix.add,
    ZornVectorMatrix.neg, ZornVectorMatrix.zero]

theorem bracket_skew (D E : Derivation (R := R)) :
    bracket D E = neg (bracket E D) := by
  apply ext
  intro X
  ext i <;> simp [bracket, neg, ZornVectorMatrix.sub, ZornVectorMatrix.add,
    ZornVectorMatrix.neg]

theorem bracket_add_left (D E F : Derivation (R := R)) :
    bracket (add D E) F = add (bracket D F) (bracket E F) := by
  apply ext
  intro X
  dsimp [bracket, add]
  rw [F.map_add']
  ext i <;> simp [ZornVectorMatrix.sub, ZornVectorMatrix.add,
    ZornVectorMatrix.neg] <;> ring

theorem bracket_add_right (D E F : Derivation (R := R)) :
    bracket D (add E F) = add (bracket D E) (bracket D F) := by
  apply ext
  intro X
  dsimp [bracket, add]
  rw [D.map_add']
  ext i <;> simp [ZornVectorMatrix.sub, ZornVectorMatrix.add,
    ZornVectorMatrix.neg] <;> ring

theorem bracket_smul_left (r : R) (D E : Derivation (R := R)) :
    bracket (smul r D) E = smul r (bracket D E) := by
  apply ext
  intro X
  dsimp [bracket, smul]
  rw [E.map_smul']
  ext i <;> simp [ZornVectorMatrix.sub, ZornVectorMatrix.add,
    ZornVectorMatrix.neg, ZornVectorMatrix.smul] <;> ring

theorem bracket_smul_right (r : R) (D E : Derivation (R := R)) :
    bracket D (smul r E) = smul r (bracket D E) := by
  apply ext
  intro X
  dsimp [bracket, smul]
  rw [D.map_smul']
  ext i <;> simp [ZornVectorMatrix.sub, ZornVectorMatrix.add,
    ZornVectorMatrix.neg, ZornVectorMatrix.smul] <;> ring

theorem bracket_jacobi (D E F : Derivation (R := R)) :
    add (bracket D (bracket E F))
      (add (bracket E (bracket F D)) (bracket F (bracket D E))) = zero := by
  apply ext
  intro X
  dsimp [bracket, add, zero]
  rw [D.map_sub, E.map_sub, F.map_sub]
  ext i <;>
    simp [ZornVectorMatrix.sub, ZornVectorMatrix.add,
      ZornVectorMatrix.neg, ZornVectorMatrix.zero] <;>
    ring

@[simp] theorem bracket_zero_left (D : Derivation (R := R)) :
    bracket zero D = zero := by
  apply ext
  intro X
  dsimp [bracket, zero]
  rw [D.map_zero]
  ext i <;> simp [ZornVectorMatrix.sub, ZornVectorMatrix.add,
    ZornVectorMatrix.neg, ZornVectorMatrix.zero]

@[simp] theorem bracket_zero_right (D : Derivation (R := R)) :
    bracket D zero = zero := by
  apply ext
  intro X
  dsimp [bracket, zero]
  rw [D.map_zero]
  ext i <;> simp [ZornVectorMatrix.sub, ZornVectorMatrix.add,
    ZornVectorMatrix.neg, ZornVectorMatrix.zero]

/--
A theorem-honest Lie-style surface for explicit derivations of the Zorn product.

This is a record of operations and laws, not a broad typeclass instance.  It
exposes the checked commutator algebra while keeping the non-associative Zorn
product separate from ordinary associative algebra interfaces.
-/
structure LieSurface where
  zeroOp : Derivation (R := R)
  addOp : Derivation (R := R) → Derivation (R := R) → Derivation (R := R)
  negOp : Derivation (R := R) → Derivation (R := R)
  smulOp : R → Derivation (R := R) → Derivation (R := R)
  bracketOp : Derivation (R := R) → Derivation (R := R) → Derivation (R := R)
  mapOne : ∀ (D : Derivation (R := R)), D one = ZornVectorMatrix.zero
  mapScalar : ∀ (D : Derivation (R := R)) (r : R), D (scalar r) = ZornVectorMatrix.zero
  mapConj : ∀ (D : Derivation (R := R)) X, D (conj X) = ZornVectorMatrix.neg (D X)
  conjNormLeft : ∀ (D : Derivation (R := R)) X,
    ZornVectorMatrix.add (mul (D X) (conj X)) (mul X (D (conj X))) =
      ZornVectorMatrix.zero
  conjNormRight : ∀ (D : Derivation (R := R)) X,
    ZornVectorMatrix.add (mul (D (conj X)) X) (mul (conj X) (D X)) =
      ZornVectorMatrix.zero
  addComm : ∀ D E, addOp D E = addOp E D
  addAssoc : ∀ D E F, addOp (addOp D E) F = addOp D (addOp E F)
  addZero : ∀ D, addOp D zeroOp = D
  zeroAdd : ∀ D, addOp zeroOp D = D
  addLeftNeg : ∀ D, addOp (negOp D) D = zeroOp
  smulZero : ∀ r, smulOp r zeroOp = zeroOp
  zeroSmul : ∀ D, smulOp 0 D = zeroOp
  oneSmul : ∀ D, smulOp 1 D = D
  smulAdd : ∀ r D E, smulOp r (addOp D E) =
    addOp (smulOp r D) (smulOp r E)
  addSmul : ∀ r s D, smulOp (r + s) D =
    addOp (smulOp r D) (smulOp s D)
  smulSmul : ∀ r s D, smulOp r (smulOp s D) = smulOp (r * s) D
  bracketSelf : ∀ D, bracketOp D D = zeroOp
  bracketSkew : ∀ D E, bracketOp D E = negOp (bracketOp E D)
  bracketAddLeft : ∀ D E F, bracketOp (addOp D E) F =
    addOp (bracketOp D F) (bracketOp E F)
  bracketAddRight : ∀ D E F, bracketOp D (addOp E F) =
    addOp (bracketOp D E) (bracketOp D F)
  bracketSmulLeft : ∀ r D E, bracketOp (smulOp r D) E =
    smulOp r (bracketOp D E)
  bracketSmulRight : ∀ r D E, bracketOp D (smulOp r E) =
    smulOp r (bracketOp D E)
  bracketJacobi : ∀ D E F,
    addOp (bracketOp D (bracketOp E F))
      (addOp (bracketOp E (bracketOp F D)) (bracketOp F (bracketOp D E))) =
      zeroOp

/-- The explicit Lie-style surface carried by derivations of the Zorn product. -/
def lieSurface : LieSurface (R := R) where
  zeroOp := zero
  addOp := add
  negOp := neg
  smulOp := smul
  bracketOp := bracket
  mapOne := map_one
  mapScalar := map_scalar
  mapConj := map_conj_eq_neg
  conjNormLeft := derivation_conj_norm_identity_left
  conjNormRight := derivation_conj_norm_identity_right
  addComm := add_comm
  addAssoc := add_assoc
  addZero := add_zero
  zeroAdd := zero_add
  addLeftNeg := add_left_neg
  smulZero := smul_zero
  zeroSmul := zero_smul
  oneSmul := one_smul
  smulAdd := smul_add
  addSmul := add_smul
  smulSmul := smul_smul
  bracketSelf := bracket_self
  bracketSkew := bracket_skew
  bracketAddLeft := bracket_add_left
  bracketAddRight := bracket_add_right
  bracketSmulLeft := bracket_smul_left
  bracketSmulRight := bracket_smul_right
  bracketJacobi := bracket_jacobi

@[simp] theorem lieSurface_zeroOp :
    (lieSurface (R := R)).zeroOp = zero :=
  rfl

@[simp] theorem lieSurface_addOp (D E : Derivation (R := R)) :
    (lieSurface (R := R)).addOp D E = add D E :=
  rfl

@[simp] theorem lieSurface_negOp (D : Derivation (R := R)) :
    (lieSurface (R := R)).negOp D = neg D :=
  rfl

@[simp] theorem lieSurface_smulOp (r : R) (D : Derivation (R := R)) :
    (lieSurface (R := R)).smulOp r D = smul r D :=
  rfl

@[simp] theorem lieSurface_bracketOp (D E : Derivation (R := R)) :
    (lieSurface (R := R)).bracketOp D E = bracket D E :=
  rfl

instance : Add (Derivation (R := R)) := ⟨add⟩

instance : Zero (Derivation (R := R)) := ⟨zero⟩

instance : Neg (Derivation (R := R)) := ⟨neg⟩

instance : Sub (Derivation (R := R)) := ⟨sub⟩

instance : AddGroup (Derivation (R := R)) :=
  AddGroup.ofLeftAxioms add_assoc zero_add add_left_neg

instance : AddCommGroup (Derivation (R := R)) :=
  AddCommGroup.mk add_comm

instance : SMul R (Derivation (R := R)) := ⟨smul⟩

instance : SemigroupAction R (Derivation (R := R)) :=
  SemigroupAction.mk (by
    intro r s D
    change (r * s) • D = r • (s • D)
    simpa using (smul_smul (r := r) (s := s) (D := D)).symm)

instance : MulAction R (Derivation (R := R)) :=
  MulAction.mk (by
    intro D
    change (1 : R) • D = D
    simpa using (one_smul (D := D)))

instance : DistribMulAction R (Derivation (R := R)) :=
  DistribMulAction.mk (by
    intro r
    change r • (0 : Derivation (R := R)) = 0
    simpa using (smul_zero (r := r))) (by
    intro r D E
    change r • (D + E) = r • D + r • E
    simpa using (smul_add (r := r) (D := D) (E := E)))

instance : Module R (Derivation (R := R)) :=
  Module.mk (by
    intro r s D
    change (r + s) • D = r • D + s • D
    simpa using (add_smul (r := r) (s := s) (D := D))) (by
    intro D
    change (0 : R) • D = 0
    simpa using (zero_smul (D := D)))

instance : LieRing (Derivation (R := R)) :=
  { bracket := bracket
    add_lie := bracket_add_left
    lie_add := bracket_add_right
    lie_self := bracket_self
    leibniz_lie := by
      intro D E F
      have h1 : bracket E (bracket F D) = - bracket E (bracket D F) := by
        have h1a : bracket E (bracket F D) =
            bracket E (smul (-1 : R) (bracket D F)) := by
          simpa [neg_eq_smul_neg_one] using congrArg (bracket E) (bracket_skew F D)
        have h1b : bracket E (smul (-1 : R) (bracket D F)) =
            - bracket E (bracket D F) := by
          calc
            bracket E (smul (-1 : R) (bracket D F)) =
                smul (-1 : R) (bracket E (bracket D F)) := by
              simpa using (bracket_smul_right (-1 : R) E (bracket D F))
            _ = - bracket E (bracket D F) := by
              rw [← neg_eq_smul_neg_one]
              rfl
        exact h1a.trans h1b
      have h2 : bracket F (bracket D E) = - bracket (bracket D E) F := by
        calc
          bracket F (bracket D E) =
              smul (-1 : R) (bracket (bracket D E) F) := by
            simpa using (bracket_skew F (bracket D E))
          _ = - bracket (bracket D E) F := by
            rw [← neg_eq_smul_neg_one]
            rfl
      have h0 := bracket_jacobi D E F
      rw [h1, h2] at h0
      have h :
          bracket D (bracket E F) +
              (-(bracket E (bracket D F)) + -(bracket (bracket D E) F)) = 0 := by
        simpa [add_assoc, add_left_comm, add_comm] using h0
      have h' := eq_neg_of_add_eq_zero_left h
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
  }

instance : LieAlgebra R (Derivation (R := R)) :=
  LieAlgebra.mk (by
    intro t D E
    change bracket D (smul t E) = smul t (bracket D E)
    simpa using (bracket_smul_right t D E))

end Derivation

/-!
The theorem packet above keeps scalar multiplication and multiplication
explicit rather than installing a `Ring` instance.  This is intentional: the
Zorn product is distributive and has a norm-composition law, but it is not
associative.
-/

def coordEquiv : ZornVectorMatrix R ≃ (R × (Fin 3 → R) × (Fin 3 → R) × R) where
  toFun X := (X.a, X.v, X.w, X.b)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv X := by cases X; rfl
  right_inv t := by rcases t with ⟨a, v, w, b⟩; rfl

instance : Add (ZornVectorMatrix R) := ⟨add⟩
instance : Zero (ZornVectorMatrix R) := ⟨zero⟩
instance : Neg (ZornVectorMatrix R) := ⟨neg⟩

instance : AddCommGroup (ZornVectorMatrix R) :=
  Equiv.addCommGroup coordEquiv

instance : SMul R (ZornVectorMatrix R) := ⟨smul⟩

instance : Module R (ZornVectorMatrix R) :=
  Equiv.module R coordEquiv

/-- A concrete rational Cartan coordinate. -/
def cartanChargeFn (X : ZornVectorMatrix ℚ) : ℚ := X.a

def cartanCharge : ZornVectorMatrix ℚ →ₗ[ℚ] ℚ where
  toFun := cartanChargeFn
  map_add' := by intro X Y; rfl
  map_smul' := by intro r X; rfl

/-- The finite charge labels used by this explicitly specified state sector. -/
def chargeValue : Fin 6 → ℚ :=
  ![0, -1, 1 / 3, -(1 / 3), 2 / 3, -(2 / 3)]

def chargeState (i : Fin 6) : ZornVectorMatrix ℚ :=
  diagonal (chargeValue i) 0

theorem cartanCharge_state (i : Fin 6) :
    cartanCharge (chargeState i) = chargeValue i := rfl

theorem charge_image :
    Set.range (fun i : Fin 6 => cartanCharge (chargeState i)) =
      ({0, -1, 1 / 3, -(1 / 3), 2 / 3, -(2 / 3)} : Set ℚ) := by
  ext q
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [cartanCharge, cartanChargeFn, chargeState, chargeValue, diagonal]
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩

end ZornVectorMatrix
end InfoGeometry.Algebra
