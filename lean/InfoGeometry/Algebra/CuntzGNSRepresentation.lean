import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Native algebraic GNS carrier for the Cuntz quotient

This file works on the noncommutative carrier `CuntzAlg n`.  It does not
replace a positive functional by a finite diagonal coefficient vector.
Positivity and completion belong to the native C*-algebra/GNS owner; this file
supplies the algebraic sesquilinear expression and the left-regular action.
-/

open InfoGeometry.Algebra.CuntzTensorQuotient
open scoped ComplexConjugate

noncomputable section

namespace InfoGeometry.Algebra.CuntzGNSRepresentation

variable {n : ℕ}

/-- Embed finite coefficients as an actual element of the Cuntz quotient. -/
def diagonalElement (n : ℕ) (c : Fin n → ℂ) : CuntzAlg n :=
  ∑ i : Fin n, c i • (cuntzS n i * cuntzSdag n i)

@[simp] theorem diagonalElement_zero (n : ℕ) :
    diagonalElement n (fun _ => 0) = 0 := by
  simp [diagonalElement]

/-- The algebraic GNS form induced by a linear functional on `CuntzAlg n`. -/
def kmsInner
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (a b : CuntzAlg n) : ℂ :=
  φ (star b * a)

/-- Hermiticity of the induced form under the exact native *-functional law. -/
theorem kmsInner_hermitian
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (hφ : ∀ a b : CuntzAlg n,
      star (φ (star a * b)) = φ (star b * a))
    (a b : CuntzAlg n) :
    star (kmsInner φ b a) = kmsInner φ a b := by
  exact hφ a b

/-- Left multiplication on the algebraic Cuntz quotient. -/
noncomputable def leftMultiplication
    (n : ℕ) (a : CuntzAlg n) : CuntzAlg n →ₗ[ℂ] CuntzAlg n :=
  LinearMap.mulLeft ℂ a

@[simp] theorem leftMultiplication_apply
    (n : ℕ) (a x : CuntzAlg n) :
    leftMultiplication n a x = a * x := by
  rfl

theorem leftMultiplication_mul
    (n : ℕ) (a b : CuntzAlg n) (x : CuntzAlg n) :
    leftMultiplication n a (leftMultiplication n b x) =
      leftMultiplication n (a * b) x := by
  simp [leftMultiplication, LinearMap.mulLeft_apply, mul_assoc]

theorem leftMultiplication_cuntz_isometry
    (n : ℕ) (i : Fin n) (x : CuntzAlg n) :
    leftMultiplication n (cuntzSdag n i)
        (leftMultiplication n (cuntzS n i) x) = x := by
  rw [leftMultiplication_mul, cuntz_isometry]
  simp [leftMultiplication]

theorem leftMultiplication_cuntz_qccr_zero
    (n : ℕ) (i : Fin n) (x : CuntzAlg n) :
    leftMultiplication n (cuntzSdag n i)
        (leftMultiplication n (cuntzS n i) x) - x = 0 := by
  rw [leftMultiplication_cuntz_isometry]
  exact sub_self x

end InfoGeometry.Algebra.CuntzGNSRepresentation
