/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Group.Commute.Units
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A faithful quadratic matrix algebra with an involutive coefficient twist

For a commutative coefficient ring `R`, an involutive ring automorphism `σ`,
and a coefficient `T` fixed by `σ`, the matrices

`!![a, b * T; σ b, σ a]`

form a native subring of the generally noncommutative two by two matrix ring.
Their trace and determinant are fixed coefficients, hence central in this
subring, and every element satisfies the resulting quadratic identity.

No invertibility of `T` is needed for these identities or for faithfulness of
the coordinate map. Without that additional assumption, the glide need not be
a unit. No universal Ore presentation, Laurent invariant-ring classification,
Galois extension, Azumaya property, or topological assertion is made here.
-/

namespace InfoGeometry.Algebra.QuadraticCrossedProduct

variable {R : Type*} [CommRing R]

/-- The faithful matrix coordinates of a twisted quadratic algebra. -/
def matrix (σ : R ≃+* R) (T a b : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, b * T; σ b, σ a]

variable (σ : R ≃+* R) (T : R)

/-- Faithfulness does not require a unit or a non-zero-divisor hypothesis on `T`. -/
theorem matrix_injective :
    Function.Injective (fun p : R × R => matrix σ T p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  · apply σ.injective
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 0) h

@[simp] theorem matrix_zero : matrix σ T 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

@[simp] theorem matrix_one : matrix σ T 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

theorem matrix_add (a b c d : R) :
    matrix σ T (a + c) (b + d) = matrix σ T a b + matrix σ T c d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, add_mul]

theorem matrix_neg (a b : R) :
    matrix σ T (-a) (-b) = -matrix σ T a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

/-- Ordered matrix multiplication gives the twisted coefficient product. -/
theorem matrix_mul (hσ : Function.Involutive σ) (hT : σ T = T)
    (a b c d : R) :
    matrix σ T a b * matrix σ T c d =
      matrix σ T (a * c + b * σ d * T) (a * d + b * σ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_two, hσ c, hσ d, hT] <;> ring

/-- The actual matrix image, with the ring operations inherited from matrices. -/
def quadraticSubring (hσ : Function.Involutive σ) (hT : σ T = T) :
    Subring (Matrix (Fin 2) (Fin 2) R) where
  carrier := {M | ∃ a b, matrix σ T a b = M}
  zero_mem' := ⟨0, 0, matrix_zero σ T⟩
  one_mem' := ⟨1, 0, matrix_one σ T⟩
  add_mem' := by
    rintro M N ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, matrix_add σ T a b c d⟩
  neg_mem' := by
    rintro M ⟨a, b, rfl⟩
    exact ⟨-a, -b, matrix_neg σ T a b⟩
  mul_mem' := by
    rintro M N ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a * c + b * σ d * T, a * d + b * σ c,
      (matrix_mul σ T hσ hT a b c d).symm⟩

variable (hσ : Function.Involutive σ) (hT : σ T = T)

/-- An element of the native subring, with its two coefficient coordinates. -/
def ofCoefficients (a b : R) : quadraticSubring σ T hσ hT :=
  ⟨matrix σ T a b, a, b, rfl⟩

/-- The coefficient ring embeds into the actual quadratic matrix subring. -/
def coefficientEmbedding : R →+* quadraticSubring σ T hσ hT where
  toFun a := ofCoefficients σ T hσ hT a 0
  map_one' := by
    apply Subtype.ext
    exact matrix_one σ T
  map_mul' a b := by
    apply Subtype.ext
    change matrix σ T (a * b) 0 = matrix σ T a 0 * matrix σ T b 0
    rw [matrix_mul σ T hσ hT]
    simp
  map_zero' := by
    apply Subtype.ext
    exact matrix_zero σ T
  map_add' a b := by
    apply Subtype.ext
    change matrix σ T (a + b) 0 = matrix σ T a 0 + matrix σ T b 0
    simpa using matrix_add σ T a 0 b 0

theorem coefficientEmbedding_injective :
    Function.Injective (coefficientEmbedding σ T hσ hT) := by
  intro a b h
  exact congrArg
    (fun x : quadraticSubring σ T hσ hT =>
      (x : Matrix (Fin 2) (Fin 2) R) 0 0) h

/-- The quadratic generator. It is not assumed to be an involution or a unit. -/
def glide : quadraticSubring σ T hσ hT :=
  ofCoefficients σ T hσ hT 0 1

/-- The glide square is the embedded fixed coefficient `T`. -/
theorem glide_mul_glide :
    glide σ T hσ hT * glide σ T hσ hT =
      coefficientEmbedding σ T hσ hT T := by
  apply Subtype.ext
  change matrix σ T 0 1 * matrix σ T 0 1 = matrix σ T T 0
  rw [matrix_mul σ T hσ hT]
  simp

/-- A unit parameter gives a unit glide in the actual quadratic subring. -/
theorem glide_isUnit (hunit : IsUnit T) : IsUnit (glide σ T hσ hT) := by
  apply (isUnit_pow_iff (show (2 : ℕ) ≠ 0 by decide)).mp
  simpa only [pow_two, glide_mul_glide] using
    hunit.map (coefficientEmbedding σ T hσ hT)

/-- The coefficient automorphism is implemented by the glide relation. -/
theorem glide_mul_coefficient (a : R) :
    glide σ T hσ hT * coefficientEmbedding σ T hσ hT a =
      coefficientEmbedding σ T hσ hT (σ a) * glide σ T hσ hT := by
  apply Subtype.ext
  change matrix σ T 0 1 * matrix σ T a 0 =
    matrix σ T (σ a) 0 * matrix σ T 0 1
  rw [matrix_mul σ T hσ hT, matrix_mul σ T hσ hT]
  simp

/-- Coefficient commutation detects the fixed ring, with no cancellation by `T`. -/
theorem glide_commutes_coefficient_iff (a : R) :
    glide σ T hσ hT * coefficientEmbedding σ T hσ hT a =
        coefficientEmbedding σ T hσ hT a * glide σ T hσ hT ↔
      σ a = a := by
  constructor
  · intro h
    have hentry := congrArg
      (fun x : quadraticSubring σ T hσ hT =>
        (x : Matrix (Fin 2) (Fin 2) R) 1 0) h
    simpa [glide, coefficientEmbedding, ofCoefficients, matrix,
      Matrix.mul_apply, Fin.sum_univ_two] using hentry.symm
  · intro ha
    rw [glide_mul_coefficient, ha]

/-- Fixed coefficients commute with every matrix in the constructed algebra. -/
theorem coefficient_matrix_commutes (hσ : Function.Involutive σ) (hT : σ T = T)
    (c a b : R) (hc : σ c = c) :
    matrix σ T c 0 * matrix σ T a b =
      matrix σ T a b * matrix σ T c 0 := by
  rw [matrix_mul σ T hσ hT, matrix_mul σ T hσ hT]
  simp only [map_zero, zero_mul, mul_zero, add_zero, zero_add, hc]
  congr 1 <;> ring

/-- Among coefficient elements, centrality is exactly invariance under `σ`. -/
theorem coefficient_mem_center_iff (a : R) :
    coefficientEmbedding σ T hσ hT a ∈
        Subring.center (quadraticSubring σ T hσ hT) ↔
      σ a = a := by
  rw [Subring.mem_center_iff]
  constructor
  · intro h
    exact (glide_commutes_coefficient_iff σ T hσ hT a).mp
      (h (glide σ T hσ hT))
  · intro ha x
    obtain ⟨b, c, hx⟩ := x.property
    apply Subtype.ext
    change (x : Matrix (Fin 2) (Fin 2) R) * matrix σ T a 0 =
      matrix σ T a 0 * (x : Matrix (Fin 2) (Fin 2) R)
    rw [← hx]
    exact (coefficient_matrix_commutes σ T hσ hT a b c ha).symm

/-- The fixed coefficient that becomes the matrix trace. -/
def traceCoefficient (a : R) : R := a + σ a

/-- The fixed coefficient that becomes the matrix determinant. -/
def normCoefficient (a b : R) : R := a * σ a - b * σ b * T

theorem matrix_trace (a b : R) :
    Matrix.trace (matrix σ T a b) = traceCoefficient σ a := by
  simp [Matrix.trace_fin_two, matrix, traceCoefficient]

theorem matrix_det (a b : R) :
    Matrix.det (matrix σ T a b) = normCoefficient σ T a b := by
  simp [Matrix.det_fin_two, matrix, normCoefficient]
  ring

theorem traceCoefficient_fixed (hσ : Function.Involutive σ) (a : R) :
    σ (traceCoefficient σ a) = traceCoefficient σ a := by
  simp only [traceCoefficient, map_add, hσ a]
  exact add_comm _ _

theorem normCoefficient_fixed (hσ : Function.Involutive σ) (hT : σ T = T)
    (a b : R) :
    σ (normCoefficient σ T a b) = normCoefficient σ T a b := by
  simp only [normCoefficient, map_sub, map_mul, hσ a, hσ b, hT]
  ring

/-- The native matrix trace embeds into the center of the quadratic subring. -/
theorem trace_mem_center (x : quadraticSubring σ T hσ hT) :
    coefficientEmbedding σ T hσ hT
        (Matrix.trace (x : Matrix (Fin 2) (Fin 2) R)) ∈
      Subring.center (quadraticSubring σ T hσ hT) := by
  apply (coefficient_mem_center_iff σ T hσ hT _).mpr
  obtain ⟨a, b, hx⟩ := x.property
  rw [← hx, matrix_trace]
  exact traceCoefficient_fixed σ hσ a

/-- The native matrix determinant embeds into the center of the quadratic subring. -/
theorem norm_mem_center (x : quadraticSubring σ T hσ hT) :
    coefficientEmbedding σ T hσ hT
        (Matrix.det (x : Matrix (Fin 2) (Fin 2) R)) ∈
      Subring.center (quadraticSubring σ T hσ hT) := by
  apply (coefficient_mem_center_iff σ T hσ hT _).mpr
  obtain ⟨a, b, hx⟩ := x.property
  rw [← hx, matrix_det]
  exact normCoefficient_fixed σ T hσ hT a b

/-- Cayley--Hamilton in ordered matrix products with the fixed coefficients embedded. -/
theorem matrix_quadratic_identity (hσ : Function.Involutive σ) (hT : σ T = T)
    (a b : R) :
    matrix σ T a b * matrix σ T a b -
        matrix σ T (traceCoefficient σ a) 0 * matrix σ T a b +
        matrix σ T (normCoefficient σ T a b) 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, traceCoefficient, normCoefficient, hσ a, hσ b, hT] <;> ring

/-- Every element of the actual subring satisfies its central quadratic identity. -/
theorem quadratic_identity (x : quadraticSubring σ T hσ hT) :
    x * x - coefficientEmbedding σ T hσ hT
        (Matrix.trace (x : Matrix (Fin 2) (Fin 2) R)) * x +
        coefficientEmbedding σ T hσ hT
          (Matrix.det (x : Matrix (Fin 2) (Fin 2) R)) = 0 := by
  obtain ⟨a, b, hx⟩ := x.property
  apply Subtype.ext
  change (x : Matrix (Fin 2) (Fin 2) R) * (x : Matrix (Fin 2) (Fin 2) R) -
      matrix σ T (Matrix.trace (x : Matrix (Fin 2) (Fin 2) R)) 0 *
        (x : Matrix (Fin 2) (Fin 2) R) +
      matrix σ T (Matrix.det (x : Matrix (Fin 2) (Fin 2) R)) 0 = 0
  rw [← hx, matrix_trace, matrix_det]
  exact matrix_quadratic_identity σ T hσ hT a b

end InfoGeometry.Algebra.QuadraticCrossedProduct

/-! ## A noncommutative instance of the actual quadratic image

The imported matrix-unit owner supplies the generic ambient matrix witness.
This concrete conjugation instance additionally witnesses noncommutativity
inside the image just constructed. Identity twists can give commutative images.
-/

namespace InfoGeometry.Algebra.QuadraticCrossedProduct

/-- The glide in the conjugation example of the quadratic matrix construction. -/
noncomputable def complexGlideMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  matrix Complex.conjAe.toRingEquiv 1 0 1

/-- The embedded imaginary coefficient in the same quadratic matrix construction. -/
noncomputable def complexCoefficientIMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  matrix Complex.conjAe.toRingEquiv 1 Complex.I 0

/-- A closed noncommutativity witness inside the actual quadratic matrix image. -/
theorem complex_glide_coefficient_noncommutative :
    complexGlideMatrix * complexCoefficientIMatrix ≠
      complexCoefficientIMatrix * complexGlideMatrix := by
  let σ : ℂ ≃+* ℂ := Complex.conjAe.toRingEquiv
  have hσ : Function.Involutive σ := fun z => Complex.conj_conj z
  have hT : σ (1 : ℂ) = 1 := map_one σ
  intro h
  have hsubring :
      glide σ 1 hσ hT * coefficientEmbedding σ 1 hσ hT Complex.I =
        coefficientEmbedding σ 1 hσ hT Complex.I * glide σ 1 hσ hT := by
    apply Subtype.ext
    exact h
  have hI := (glide_commutes_coefficient_iff σ 1 hσ hT Complex.I).mp hsubring
  have him : (-1 : ℝ) = 1 := congrArg Complex.im hI
  norm_num at him

end InfoGeometry.Algebra.QuadraticCrossedProduct
