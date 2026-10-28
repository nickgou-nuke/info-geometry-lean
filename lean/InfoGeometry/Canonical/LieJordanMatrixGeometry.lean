/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.LieJordanComposition
import InfoGeometry.Core.OperatorCliffordDouble
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Basic

/-!
# Full matrix trace geometry and doubled Lie–Jordan operators

The symmetric bilinear trace form and the conjugate-transpose trace pairing
remain distinct. The latter gives a negative quadratic identity under explicit
star assumptions. The final construction doubles the actual endomorphisms of
the matrix space; it never substitutes the coefficient matrices for them.
-/

namespace InfoGeometry.Canonical.LieJordanMatrixGeometry

open scoped Matrix

open InfoGeometry.Core.LieJordanComposition
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.Core.OperatorCliffordDouble

attribute [local instance 100] LieRing.ofAssociativeRing

section BilinearTrace

variable {K n : Type*} [CommRing K] [Fintype n] [DecidableEq n]

/-- The native bilinear form induced by multiplication and matrix trace. -/
def traceBilinear : LinearMap.BilinForm K (Matrix n n K) :=
  (LinearMap.mul K (Matrix n n K)).compr₂ (Matrix.traceLinearMap n K K)

@[simp] theorem traceBilinear_apply (x y : Matrix n n K) :
    traceBilinear x y = Matrix.trace (x * y) := rfl

theorem traceBilinear_symmetric (x y : Matrix n n K) :
    traceBilinear x y = traceBilinear y x := Matrix.trace_mul_comm x y

/-- Nondegeneracy tests against every matrix; it does not assert anisotropy. -/
theorem traceBilinear_nondegenerate :
    (traceBilinear (K := K) (n := n)).Nondegenerate := by
  constructor
  · intro x hx
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro y
    simpa only [traceBilinear_apply, zero_mul, Matrix.trace_zero] using hx y
  · intro y hy
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro x
    simpa only [traceBilinear_apply, mul_zero, Matrix.trace_zero] using hy x

theorem traceBilinear_plus_minus (h s x y : Matrix n n K) :
    traceBilinear (plus (R := K) h s x) y +
      traceBilinear x (minus (R := K) h s y) = 0 :=
  trace_plus_minus (R := K) (Matrix.traceAddMonoidHom n K)
    Matrix.trace_mul_comm h s x y

/-- Removing the exact trace drift produces a trace-zero tangent at trace one. -/
theorem normalized_plus_trace_zero (h s x : Matrix n n K) (hx : Matrix.trace x = 1) :
    Matrix.trace (plus (R := K) h s x - (2 * Matrix.trace (s * x)) • x) = 0 := by
  have ht : Matrix.trace (plus (R := K) h s x) = 2 • Matrix.trace (s * x) :=
    trace_plus (R := K) (Matrix.traceAddMonoidHom n K) Matrix.trace_mul_comm h s x
  rw [Matrix.trace_sub, Matrix.trace_smul, ht, hx]
  simp [two_mul]

end BilinearTrace

section HilbertSchmidtTrace

open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem conjTranspose_ad (h x : Matrix n n ℂ) :
    (LieAlgebra.ad ℂ (Matrix n n ℂ) h x)ᴴ =
      -(LieAlgebra.ad ℂ (Matrix n n ℂ) hᴴ xᴴ) := by
  change (h * x - x * h)ᴴ = -(hᴴ * xᴴ - xᴴ * hᴴ)
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  abel

theorem conjTranspose_jordan (s x : Matrix n n ℂ) :
    (jordanLeft (R := ℂ) s x)ᴴ = jordanLeft (R := ℂ) sᴴ xᴴ := by
  change (s * x + x * s)ᴴ = sᴴ * xᴴ + xᴴ * sᴴ
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul]
  abel

/-- The Hilbert–Schmidt adjoint of the inner action has the starred coefficient. -/
theorem trace_ad_hilbertSchmidt (h x y : Matrix n n ℂ) :
    Matrix.trace ((LieAlgebra.ad ℂ (Matrix n n ℂ) h x)ᴴ * y) =
      Matrix.trace (xᴴ * LieAlgebra.ad ℂ (Matrix n n ℂ) hᴴ y) := by
  rw [conjTranspose_ad, neg_mul, Matrix.trace_neg]
  have hz := trace_ad_skew (R := ℂ) (Matrix.traceAddMonoidHom n ℂ)
    Matrix.trace_mul_comm hᴴ xᴴ y
  change Matrix.trace (LieAlgebra.ad ℂ (Matrix n n ℂ) hᴴ xᴴ * y) +
    Matrix.trace (xᴴ * LieAlgebra.ad ℂ (Matrix n n ℂ) hᴴ y) = 0 at hz
  apply neg_eq_of_add_eq_zero_left
  simpa only [add_comm] using hz

theorem trace_jordan_hilbertSchmidt (s x y : Matrix n n ℂ) :
    Matrix.trace ((jordanLeft (R := ℂ) s x)ᴴ * y) =
      Matrix.trace (xᴴ * jordanLeft (R := ℂ) sᴴ y) := by
  rw [conjTranspose_jordan]
  exact trace_jordan_symmetric (R := ℂ) (Matrix.traceAddMonoidHom n ℂ)
    Matrix.trace_mul_comm sᴴ xᴴ y

theorem trace_plus_hilbertSchmidt (h s x y : Matrix n n ℂ) :
    Matrix.trace ((plus (R := ℂ) h s x)ᴴ * y) =
      Matrix.trace (xᴴ * plus (R := ℂ) hᴴ sᴴ y) := by
  change Matrix.trace ((LieAlgebra.ad ℂ (Matrix n n ℂ) h x +
      jordanLeft (R := ℂ) s x)ᴴ * y) =
    Matrix.trace (xᴴ * (LieAlgebra.ad ℂ (Matrix n n ℂ) hᴴ y +
      jordanLeft (R := ℂ) sᴴ y))
  rw [Matrix.conjTranspose_add, add_mul, mul_add, Matrix.trace_add, Matrix.trace_add,
    trace_ad_hilbertSchmidt, trace_jordan_hilbertSchmidt]

/-- Negative adjunction requires a skew-Hermitian Lie coefficient and a
Hermitian Jordan coefficient, with no assumption that they commute. -/
theorem trace_hilbertSchmidt_plus_minus (h s x y : Matrix n n ℂ)
    (hh : hᴴ = -h) (hs : sᴴ = s) :
    Matrix.trace ((plus (R := ℂ) h s x)ᴴ * y) +
      Matrix.trace (xᴴ * minus (R := ℂ) h s y) = 0 := by
  rw [trace_plus_hilbertSchmidt]
  have hp : plus (R := ℂ) hᴴ sᴴ y = -(minus (R := ℂ) h s y) := by
    rw [hh, hs, plus_apply, minus_apply]
    noncomm_ring
  rw [hp, mul_neg, Matrix.trace_neg, neg_add_cancel]

/-- The product is negative in its Hilbert–Schmidt quadratic form even when
the coefficient commutator is nonzero. -/
theorem trace_ordered_product_eq_negative_gram (h s x : Matrix n n ℂ)
    (hh : hᴴ = -h) (hs : sᴴ = s) :
    Matrix.trace (xᴴ * (minus (R := ℂ) h s * plus (R := ℂ) h s) x) =
      -Matrix.trace ((plus (R := ℂ) h s x)ᴴ * plus (R := ℂ) h s x) := by
  exact eq_neg_of_add_eq_zero_right
    (trace_hilbertSchmidt_plus_minus h s x (plus (R := ℂ) h s x) hh hs)

theorem trace_ordered_product_re_nonpos (h s x : Matrix n n ℂ)
    (hh : hᴴ = -h) (hs : sᴴ = s) :
    (Matrix.trace (xᴴ * (minus (R := ℂ) h s * plus (R := ℂ) h s) x)).re ≤ 0 := by
  rw [trace_ordered_product_eq_negative_gram h s x hh hs, Complex.neg_re]
  exact neg_nonpos.mpr (Complex.nonneg_iff.mp
    (Matrix.posSemidef_conjTranspose_mul_self (plus (R := ℂ) h s x)).trace_nonneg).1

end HilbertSchmidtTrace

section FullMatrixSynthesis

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem matrix_doubling_injective :
    Function.Injective (fun x : Matrix n n ℂ => (2 : ℕ) • x) := by
  intro x y h
  ext i j
  have hij := congrArg (fun z : Matrix n n ℂ => z i j) h
  simp only [two_nsmul, Matrix.add_apply] at hij
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
    (by simpa only [two_mul] using hij)

/-- Faithful Clifford lifting preserves exactly the input noncommutativity. -/
theorem lifted_pair_commute_iff (h s : Matrix n n ℂ) :
    Commute (lift (plus (R := ℂ) h s)) (lift (minus (R := ℂ) h s)) ↔ Commute h s := by
  rw [lift_commute_iff, plus_minus_commute_iff matrix_doubling_injective]

/-- The full doubled square retains the mixed Lie–Jordan correction. Its
carrier is `(Matrix n n ℂ) × (Matrix n n ℂ)`. -/
theorem doubled_pair_square (h s : Matrix n n ℂ) :
    diracPlus (minus (R := ℂ) h s) (plus (R := ℂ) h s) ^ 2 =
      block ((minus (R := ℂ) h s) ^ 2 + (plus (R := ℂ) h s) ^ 2)
        (2 • jordanLeft (R := ℂ) ⁅h, s⁆)
        (-(2 • jordanLeft (R := ℂ) ⁅h, s⁆))
        ((minus (R := ℂ) h s) ^ 2 + (plus (R := ℂ) h s) ^ 2) := by
  rw [diracPlus_sq, ordered_products_sub]

theorem doubled_pair_upperRight (h s : Matrix n n ℂ) :
    upperRight (diracPlus (minus (R := ℂ) h s) (plus (R := ℂ) h s) ^ 2) =
      2 • jordanLeft (R := ℂ) ⁅h, s⁆ := by
  rw [doubled_pair_square, upperRight_block]

/-- Removing the doubled square correction is possible exactly for commuting inputs. -/
theorem doubled_pair_upperRight_eq_zero_iff (h s : Matrix n n ℂ) :
    upperRight (diracPlus (minus (R := ℂ) h s) (plus (R := ℂ) h s) ^ 2) = 0 ↔
      Commute h s := by
  rw [upperRight_diracPlus_sq_eq_zero_iff]
  constructor
  · intro hc
    exact (plus_minus_commute_iff matrix_doubling_injective h s).mp hc.symm
  · intro hc
    exact ((plus_minus_commute_iff matrix_doubling_injective h s).mpr hc).symm

end FullMatrixSynthesis

end InfoGeometry.Canonical.LieJordanMatrixGeometry
