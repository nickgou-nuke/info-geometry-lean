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

theorem kmsInner_add_left
    (φ : CuntzAlg n →ₗ[ℂ] ℂ) (a₁ a₂ b : CuntzAlg n) :
    kmsInner φ (a₁ + a₂) b =
      kmsInner φ a₁ b + kmsInner φ a₂ b := by
  unfold kmsInner
  rw [mul_add, map_add]

theorem star_smul_cuntzAlg (c : ℂ) (a : CuntzAlg n) :
    star (c • a) = c • star a := by
  obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective ℂ (CuntzRel n) a
  change star (c • cuntzMk n x) = c • star (cuntzMk n x)
  rw [← map_smul, star_cuntzMk, star_cuntzMk]
  rw [show star (c • x) = c • star x by
    rw [Algebra.smul_def]
    change dagger n ((algebraMap ℂ (CuntzTensor n)) c * x) = c • dagger n x
    rw [dagger_mul, dagger_algebraMap]
    exact (Algebra.commutes c (dagger n x)).symm]
  simp

def gnsNull (φ : CuntzAlg n →ₗ[ℂ] ℂ) (a : CuntzAlg n) : Prop :=
  kmsInner φ a a = 0

theorem gnsNull_zero (φ : CuntzAlg n →ₗ[ℂ] ℂ) :
    gnsNull φ 0 := by
  unfold gnsNull kmsInner
  rw [star_zero, zero_mul, map_zero]

theorem gnsNull_smul (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (c : ℂ) {a : CuntzAlg n} (ha : gnsNull φ a) :
    gnsNull φ (c • a) := by
  simp only [gnsNull, kmsInner] at ha ⊢
  rw [star_smul_cuntzAlg, smul_mul_assoc, mul_smul_comm,
    smul_smul, map_smul, ha]
  simp

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

theorem leftMultiplication_one (n : ℕ) :
    leftMultiplication n (1 : CuntzAlg n) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp [leftMultiplication]

theorem leftMultiplication_comp
    (n : ℕ) (a b : CuntzAlg n) :
    (leftMultiplication n a).comp (leftMultiplication n b) =
      leftMultiplication n (a * b) := by
  apply LinearMap.ext
  intro x
  simp [leftMultiplication, LinearMap.comp_apply]

theorem leftMultiplication_mul
  (n : ℕ) (a b : CuntzAlg n) (x : CuntzAlg n) :
      leftMultiplication n a (leftMultiplication n b x) =
        leftMultiplication n (a * b) x := by
    change a * (b * x) = (a * b) * x
    exact (mul_assoc a b x).symm

theorem kmsInner_leftMultiplication_star
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (a x y : CuntzAlg n) :
    kmsInner φ (leftMultiplication n a x) y =
      kmsInner φ x (leftMultiplication n (star a) y) := by
  simp [kmsInner, leftMultiplication, star_mul]
  rw [mul_assoc]

theorem kmsInner_add_right
    (φ : CuntzAlg n →ₗ[ℂ] ℂ) (a b₁ b₂ : CuntzAlg n) :
    kmsInner φ a (b₁ + b₂) =
      kmsInner φ a b₁ + kmsInner φ a b₂ := by
  unfold kmsInner
  rw [star_add, add_mul, map_add]

/-! The adjoint relation iterates over products.  This is the algebraic
pre-GNS form of the fact that the left regular representation reverses the
involution when taking adjoints. -/

theorem kmsInner_leftMultiplication_mul
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (a b x y : CuntzAlg n) :
    kmsInner φ (leftMultiplication n (a * b) x) y =
      kmsInner φ x (leftMultiplication n (star b * star a) y) := by
  rw [← leftMultiplication_comp, ← leftMultiplication_comp]
  simp only [LinearMap.comp_apply]
  rw [kmsInner_leftMultiplication_star φ a]
  rw [kmsInner_leftMultiplication_star φ b]

theorem leftMultiplication_cuntz_isometry
    (n : ℕ) (i : Fin n) (x : CuntzAlg n) :
    leftMultiplication n (cuntzSdag n i)
        (leftMultiplication n (cuntzS n i) x) = x := by
  rw [leftMultiplication_mul, cuntz_isometry]
  simp [leftMultiplication]

theorem leftMultiplication_cuntz_orthogonal
    (n : ℕ) (i j : Fin n) (x : CuntzAlg n) :
    leftMultiplication n (cuntzSdag n i)
        (leftMultiplication n (cuntzS n j) x) =
      if i = j then x else 0 := by
  rw [leftMultiplication_mul, cuntz_orthogonality]
  split_ifs with hij
  · subst j
    simp [leftMultiplication]
  · simp [leftMultiplication]

/-- Each Cuntz generator acts isometrically for the algebraic GNS form.
This is the sesquilinear-form shadow of the relation `Sᵢ* Sᵢ = 1`. -/
theorem kmsInner_leftMultiplication_cuntz_isometry
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (i : Fin n) (x y : CuntzAlg n) :
    kmsInner φ (leftMultiplication n (cuntzS n i) x)
        (leftMultiplication n (cuntzS n i) y) =
      kmsInner φ x y := by
  rw [kmsInner_leftMultiplication_star φ (cuntzS n i)]
  rw [star_cuntzS]
  rw [leftMultiplication_cuntz_isometry]

/-- Distinct Cuntz branches are orthogonal in the algebraic GNS form. -/
theorem kmsInner_leftMultiplication_cuntz_orthogonal
    (φ : CuntzAlg n →ₗ[ℂ] ℂ)
    (i j : Fin n) (x y : CuntzAlg n) :
    kmsInner φ (leftMultiplication n (cuntzS n i) x)
        (leftMultiplication n (cuntzS n j) y) =
      if i = j then kmsInner φ x y else 0 := by
  rw [kmsInner_leftMultiplication_star φ (cuntzS n i)]
  rw [star_cuntzS]
  rw [leftMultiplication_mul]
  rw [cuntz_orthogonality]
  split_ifs with hij
  · subst j
    simp [leftMultiplication]
  · simp [leftMultiplication, kmsInner]

/-- The Cuntz range projections form a partition of the left-regular
representation, transported from `∑ Sᵢ Sᵢ* = 1`. -/
theorem leftMultiplication_cuntz_ranges_sum_one
    (n : ℕ) (x : CuntzAlg n) :
    (∑ i : Fin n,
      leftMultiplication n (cuntzS n i)
        (leftMultiplication n (cuntzSdag n i) x)) = x := by
  simp only [leftMultiplication_apply, ← mul_assoc]
  rw [← Finset.sum_mul]
  rw [cuntz_ranges_sum_one]
  simp

theorem kmsInner_cuntz_ranges_decomposition
    (φ : CuntzAlg n →ₗ[ℂ] ℂ) (x y : CuntzAlg n) :
    kmsInner φ x y =
      ∑ i : Fin n, kmsInner φ
        (leftMultiplication n (cuntzS n i)
          (leftMultiplication n (cuntzSdag n i) x)) y := by
  calc
    kmsInner φ x y = kmsInner φ
        (∑ i : Fin n,
          leftMultiplication n (cuntzS n i)
            (leftMultiplication n (cuntzSdag n i) x)) y := by
              rw [leftMultiplication_cuntz_ranges_sum_one]
    _ = ∑ i : Fin n, kmsInner φ
        (leftMultiplication n (cuntzS n i)
          (leftMultiplication n (cuntzSdag n i) x)) y := by
      unfold kmsInner
      rw [Finset.mul_sum, map_sum]

theorem kmsInner_cuntz_ranges_decomposition_right
    (φ : CuntzAlg n →ₗ[ℂ] ℂ) (x y : CuntzAlg n) :
    kmsInner φ x y =
      ∑ i : Fin n, kmsInner φ x
        (leftMultiplication n (cuntzS n i)
          (leftMultiplication n (cuntzSdag n i) y)) := by
  calc
    kmsInner φ x y = kmsInner φ x
        (∑ i : Fin n,
          leftMultiplication n (cuntzS n i)
            (leftMultiplication n (cuntzSdag n i) y)) := by
              rw [leftMultiplication_cuntz_ranges_sum_one]
    _ = ∑ i : Fin n, kmsInner φ x
        (leftMultiplication n (cuntzS n i)
          (leftMultiplication n (cuntzSdag n i) y)) := by
      unfold kmsInner
      rw [star_sum, Finset.sum_mul, map_sum]

theorem leftMultiplication_cuntz_qccr_zero
    (n : ℕ) (i : Fin n) (x : CuntzAlg n) :
    leftMultiplication n (cuntzSdag n i)
        (leftMultiplication n (cuntzS n i) x) - x = 0 := by
  rw [leftMultiplication_cuntz_isometry]
  exact sub_self x

end InfoGeometry.Algebra.CuntzGNSRepresentation
