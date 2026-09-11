import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological Hecke relations for a noncommutative braid carrier

The repository already contains algebraic Artin and Temperley--Lieb owners.
This file supplies the missing `TopCat` transport for the quadratic Hecke
relation.  The carrier and its generators are supplied as data; no claim is
made that an arbitrary Cuntz quotient automatically carries such a quotient.
-/

noncomputable section

namespace InfoGeometry.Canonical.HeckeBraidTopologicalBridge

open CategoryTheory

variable {R : Type*} [Ring R] [Algebra ℂ R]
variable [TopologicalSpace R] [ContinuousMul R]

/-- Continuous left multiplication by a fixed noncommutative element. -/
def leftMulTopCatHom (a : R) : TopCat.of R ⟶ TopCat.of R :=
  TopCat.ofHom
    (ContinuousMap.mulLeft a)

@[simp] theorem leftMulTopCatHom_apply (a x : R) :
    leftMulTopCatHom a x = a * x :=
  rfl

theorem leftMulTopCatHom_comp (a b : R) :
    leftMulTopCatHom a ≫ leftMulTopCatHom b =
      leftMulTopCatHom (b * a) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change b * (a * x) = (b * a) * x
  rw [mul_assoc]

theorem hecke1_leftTopCat_relation
    (q : ℂ) (sigma1 : R)
    (h1 : (sigma1 - algebraMap ℂ R q) *
        (sigma1 + algebraMap ℂ R q⁻¹) = 0) :
    leftMulTopCatHom
        (sigma1 + algebraMap ℂ R q⁻¹) ≫
      leftMulTopCatHom (sigma1 - algebraMap ℂ R q) =
      TopCat.ofHom (ContinuousMap.const R 0) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (sigma1 - algebraMap ℂ R q) *
      ((sigma1 + algebraMap ℂ R q⁻¹) * x) = 0
  rw [← mul_assoc, h1, zero_mul]

theorem hecke2_leftTopCat_relation
    (q : ℂ) (sigma2 : R)
    (h2 : (sigma2 - algebraMap ℂ R q) *
        (sigma2 + algebraMap ℂ R q⁻¹) = 0) :
    leftMulTopCatHom
        (sigma2 + algebraMap ℂ R q⁻¹) ≫
      leftMulTopCatHom (sigma2 - algebraMap ℂ R q) =
      TopCat.ofHom (ContinuousMap.const R 0) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (sigma2 - algebraMap ℂ R q) *
      ((sigma2 + algebraMap ℂ R q⁻¹) * x) = 0
  rw [← mul_assoc, h2, zero_mul]

theorem artin_leftTopCat_relation
    (sigma1 sigma2 : R)
    (hArtin : sigma1 * sigma2 * sigma1 = sigma2 * sigma1 * sigma2) :
    leftMulTopCatHom sigma1 ≫ leftMulTopCatHom sigma2 ≫
        leftMulTopCatHom sigma1 =
      leftMulTopCatHom sigma2 ≫ leftMulTopCatHom sigma1 ≫
        leftMulTopCatHom sigma2 := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change sigma1 * (sigma2 * (sigma1 * x)) =
    sigma2 * (sigma1 * (sigma2 * x))
  simpa only [mul_assoc] using congrArg (fun z : R => z * x) hArtin

end InfoGeometry.Canonical.HeckeBraidTopologicalBridge
