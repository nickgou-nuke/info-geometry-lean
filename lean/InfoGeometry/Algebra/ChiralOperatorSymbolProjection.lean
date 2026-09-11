import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Symbol projections of an associative operator envelope

An associative operator algebra may have a finite symbolic readout.  The
projected product is defined by reading an operator product back into the
symbol carrier.  The associator of that product is exactly the readout of the
discarded operator defect.
-/

namespace InfoGeometry.Algebra

variable {R Z E : Type*}
  [CommRing R]
  [AddCommGroup Z] [Module R Z]
  [Ring E] [Algebra R E]

def symbolProjection
    (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z) : E →ₗ[R] E :=
  ι.comp σ

def symbolDefect
    (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z) (X : E) : E :=
  X - symbolProjection ι σ X

def projectedOperatorMul
    (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z) (x y : Z) : Z :=
  σ (ι x * ι y)

def projectedOperatorAssociator
    (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z) (x y z : Z) : Z :=
  projectedOperatorMul ι σ
      (projectedOperatorMul ι σ x y) z -
    projectedOperatorMul ι σ x
      (projectedOperatorMul ι σ y z)

@[simp] theorem symbolProjection_apply
    (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z) (X : E) :
    symbolProjection ι σ X = ι (σ X) :=
  rfl

theorem symbolProjection_add_defect
    (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z) (X : E) :
    symbolProjection ι σ X + symbolDefect ι σ X = X := by
  simp [symbolProjection, symbolDefect]

theorem projectedOperatorAssociator_eq_defect
    (ι : Z →ₗ[R] E) (σ : E →ₗ[R] Z)
    (x y z : Z) :
    projectedOperatorAssociator ι σ x y z =
      σ (
        ι x * symbolDefect ι σ (ι y * ι z) -
          symbolDefect ι σ (ι x * ι y) * ι z) := by
  have hxy :
      symbolProjection ι σ (ι x * ι y) +
          symbolDefect ι σ (ι x * ι y) = ι x * ι y :=
    symbolProjection_add_defect ι σ (ι x * ι y)
  have hyz :
      symbolProjection ι σ (ι y * ι z) +
          symbolDefect ι σ (ι y * ι z) = ι y * ι z :=
    symbolProjection_add_defect ι σ (ι y * ι z)
  have hxy' :
      symbolProjection ι σ (ι x * ι y) =
        ι x * ι y - symbolDefect ι σ (ι x * ι y) := by
    exact (eq_sub_iff_add_eq).2 hxy
  have hyz' :
      symbolProjection ι σ (ι y * ι z) =
        ι y * ι z - symbolDefect ι σ (ι y * ι z) := by
    exact (eq_sub_iff_add_eq).2 hyz
  simp only [projectedOperatorAssociator, projectedOperatorMul]
  rw [← map_sub]
  change σ (
      symbolProjection ι σ (ι x * ι y) * ι z -
        ι x * symbolProjection ι σ (ι y * ι z)) =
    σ (
      ι x * symbolDefect ι σ (ι y * ι z) -
        symbolDefect ι σ (ι x * ι y) * ι z)
  rw [hxy', hyz']
  apply congrArg σ
  noncomm_ring

end InfoGeometry.Algebra
