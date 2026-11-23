/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.MatrixNoncommutativity

/-!
# Associative homotopes and the exact loss under symmetrization

A fixed kernel `T` changes the product of an associative ring to `x * T * y`.
The coefficient ring used for taking halves is commutative, but the operator
carrier is an arbitrary ring. No pairwise commutativity is assumed.

The generic ordered product and its commutator are distinct from the
Peirce-supported `upperHomotopeBracket` in `PeirceSpine/KantorCornerAnomaly`.
This file does not infer chronological irreversibility from a nonzero bracket.
-/

namespace InfoGeometry.Algebra.AssociativeHomotope

variable {A : Type*} [Ring A]

/-- Associative multiplication through a fixed kernel. -/
def product (T x y : A) : A := x * T * y

/-- The unnormalized commutator for the fixed-kernel product. -/
def bracket (T x y : A) : A := product T x y - product T y x

theorem product_assoc (T x y z : A) :
    product T (product T x y) z = product T x (product T y z) := by
  simp only [product, mul_assoc]

theorem product_add_left (T x y z : A) :
    product T (x + y) z = product T x z + product T y z := by
  simp only [product, add_mul]

theorem product_add_right (T x y z : A) :
    product T x (y + z) = product T x y + product T x z := by
  simp only [product, mul_add]

/-- For a unit kernel the new multiplicative identity is its inverse. -/
theorem product_inv_kernel_left (T : Aˣ) (x : A) :
    product (T : A) (↑T⁻¹ : A) x = x := by
  simp [product]

theorem product_inv_kernel_right (T : Aˣ) (x : A) :
    product (T : A) x (↑T⁻¹ : A) = x := by
  simp [product, mul_assoc]

/-- Ring maps transport the kernel as well as the two ordered inputs. -/
theorem map_product {B : Type*} [Ring B] (f : A →+* B) (T x y : A) :
    f (product T x y) = product (f T) (f x) (f y) := by
  simp [product]

/-- Multiplication by the kernel intertwines homotope and original products. -/
theorem kernel_mul_product (T x y : A) :
    T * product T x y = (T * x) * (T * y) := by
  simp only [product, mul_assoc]

@[simp] theorem bracket_self (T x : A) : bracket T x x = 0 := by
  simp [bracket]

theorem bracket_swap (T x y : A) : bracket T x y = -bracket T y x := by
  simp [bracket]

/-- The Jacobi law uses associativity and keeps every multiplication ordered. -/
theorem bracket_jacobi (T x y z : A) :
    bracket T x (bracket T y z) + bracket T y (bracket T z x) +
      bracket T z (bracket T x y) = 0 := by
  simp only [bracket, product]
  noncomm_ring

/-- Commuting with `x` is a derivation for the homotope multiplication. -/
theorem bracket_product (T x y z : A) :
    bracket T x (product T y z) =
      product T (bracket T x y) z + product T y (bracket T x z) := by
  simp only [bracket, product]
  noncomm_ring

section Halves

variable (R : Type*) [CommRing R] [Invertible (2 : R)] [Module R A]

/-- The symmetrized homotope. -/
def jordan (T x y : A) : A := (⅟2 : R) • (product T x y + product T y x)

/-- The normalized skew part, with the same factor of one half. -/
def skew (T x y : A) : A := (⅟2 : R) • bracket T x y

/-- Symmetrization cannot by itself retain an antisymmetric component. -/
theorem jordan_swap (T x y : A) : jordan R T x y = jordan R T y x := by
  simp only [jordan, add_comm]

theorem skew_swap (T x y : A) : skew R T x y = -skew R T y x := by
  rw [skew, bracket_swap, smul_neg]
  rfl

/-- Exact reconstruction of the ordered product from the two parts. -/
theorem jordan_add_skew (T x y : A) :
    jordan R T x y + skew R T x y = product T x y := by
  unfold jordan skew bracket
  rw [← smul_add]
  have h : (product T x y + product T y x) +
      (product T x y - product T y x) = product T x y + product T x y := by
    abel
  rw [h, smul_add, invOf_two_smul_add_invOf_two_smul R]

/-- The exact discarded term under symmetrization is the normalized bracket. -/
theorem product_sub_jordan (T x y : A) :
    product T x y - jordan R T x y = skew R T x y := by
  rw [← jordan_add_skew R T x y]
  abel

/-- The skew part vanishes precisely when this pair of ordered products agrees. -/
theorem skew_eq_zero_iff (T x y : A) :
    skew R T x y = 0 ↔ product T x y = product T y x := by
  constructor
  · intro h
    have h' := congrArg (fun v : A => (2 : R) • v) h
    simp only [skew, smul_smul, mul_invOf_self, one_smul, smul_zero] at h'
    exact sub_eq_zero.mp h'
  · intro h
    simp [skew, bracket, h]

/-- Equality with the symmetrization is equivalent to absence of order dependence. -/
theorem product_eq_jordan_iff (T x y : A) :
    product T x y = jordan R T x y ↔ product T x y = product T y x := by
  rw [← sub_eq_zero, product_sub_jordan, skew_eq_zero_iff]

end Halves

/-! ## Concrete two-corner realization in `Mat₂(A)`

The generic fixed-kernel product above is now realized by the ordered upper,
lower, upper matrix-corner product. These equalities retain the coefficient
ring's noncommutative multiplication order. -/

section MatrixCorners

variable {A : Type*} [Ring A]

abbrev Mat2 := Matrix (Fin 2) (Fin 2) A

/-- The upper Witt corner, with its coefficient in position `(0,1)`. -/
def upperCorner (x : A) : Mat2 (A := A) := !![0, x; 0, 0]

/-- The lower Witt corner, with its coefficient in position `(1,0)`. -/
def lowerCorner (x : A) : Mat2 (A := A) := !![0, 0; x, 0]

/-- The lower-corner vacuum used as the homotope kernel. -/
def lowerVacuum : Mat2 (A := A) := lowerCorner 1

/-- The ordered upper-lower-upper matrix product realizes the full
associative coefficient product, with no symmetrization. -/
theorem upper_lower_upper_product (x y : A) :
    upperCorner x * lowerVacuum * upperCorner y = upperCorner (x * y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperCorner, lowerVacuum, lowerCorner, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- The two mixed matrix commutators recover the ordered KKT triple
`x*z*y + y*z*x` in the upper corner. -/
theorem upper_lower_kkt_double_commutator (x z y : A) :
    (upperCorner x * lowerCorner z - lowerCorner z * upperCorner x) *
        upperCorner y -
      upperCorner y *
        (upperCorner x * lowerCorner z - lowerCorner z * upperCorner x) =
      upperCorner (x * z * y + y * z * x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperCorner, lowerCorner, sub_eq_add_neg, mul_assoc]

/-- Symmetrizing the two ordered corner products gives only the Jordan
product. The antisymmetric part remains exactly the coefficient commutator. -/
theorem upper_corner_order_difference (x y : A) :
    upperCorner x * lowerVacuum * upperCorner y -
        upperCorner y * lowerVacuum * upperCorner x =
      upperCorner (x * y - y * x) := by
  rw [upper_lower_upper_product, upper_lower_upper_product]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperCorner, Matrix.sub_apply]

/-- A noncommuting coefficient pair stays noncommuting after the ordered
homotope embedding into the full matrix algebra. -/
theorem upper_corner_order_detects_noncommutativity {x y : A}
    (hxy : x * y ≠ y * x) :
    upperCorner x * lowerVacuum * upperCorner y ≠
      upperCorner y * lowerVacuum * upperCorner x := by
  intro heq
  rw [upper_lower_upper_product, upper_lower_upper_product] at heq
  have hentry := congrArg (fun M : Mat2 (A := A) => M 0 1) heq
  have hcoeff : x * y = y * x := by simpa [upperCorner] using hentry
  exact hxy hcoeff

/-- Concrete order-sensitive instance over the repository's noncommuting
coefficient matrices. The ambient carrier is a `2×2` block matrix over the
actual noncommutative `2×2` matrix ring, hence a `4×4` real matrix algebra. -/
theorem matrixCoefficient_homotope_order_witness :
    upperCorner (A := Matrix (Fin 2) (Fin 2) ℝ)
        (InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix) *
      lowerVacuum *
        upperCorner (A := Matrix (Fin 2) (Fin 2) ℝ)
          (InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix) ≠
      upperCorner (A := Matrix (Fin 2) (Fin 2) ℝ)
          (InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix) *
        lowerVacuum *
          upperCorner (A := Matrix (Fin 2) (Fin 2) ℝ)
            (InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix) := by
  exact upper_corner_order_detects_noncommutativity
    InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix_mul_tiltedMatrix_ne

/-- Exact concrete commutator readout for the nested operator matrices. The
coefficient commutator is the nonzero skew matrix `[[0,-1],[1,0]]`, and the
outer Witt-corner product preserves it without symmetrization. -/
theorem matrixCoefficient_homotope_commutator_readout :
    upperCorner (A := Matrix (Fin 2) (Fin 2) ℝ)
        InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix *
      lowerVacuum *
        upperCorner (A := Matrix (Fin 2) (Fin 2) ℝ)
          InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix -
      upperCorner (A := Matrix (Fin 2) (Fin 2) ℝ)
          InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix *
        lowerVacuum *
          upperCorner (A := Matrix (Fin 2) (Fin 2) ℝ)
            InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix =
      upperCorner (A := Matrix (Fin 2) (Fin 2) ℝ) (!![(0 : ℝ), -1; 1, 0]) := by
  have hcoeff :
      InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix *
          InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix -
        InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix *
          InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix =
        !![(0 : ℝ), -1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix,
        InfoGeometry.Algebra.MatrixNoncommutativity.tiltedMatrix,
        Matrix.mul_apply, Fin.sum_univ_two]
  rw [upper_corner_order_difference, hcoeff]

end MatrixCorners

end InfoGeometry.Algebra.AssociativeHomotope
