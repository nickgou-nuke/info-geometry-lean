import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TrifactorSU3
import InfoGeometry.Physics.SplitOctonionBraidSU3
import InfoGeometry.Physics.QCDFureyZornProjectorBridge
import InfoGeometry.Physics.QCDZornChargeConjugationBridge

/-!
# Canonical-to-complex Zorn carrier equivalence

The repository has two theorem-bearing complex Zorn coordinate carriers:

* `InfoGeometry.Canonical.ZornMatrix ℂ`, used by the canonical projector and
  circular split-octonion lanes;
* `SplitOctonionBraidSU3.Zorn`, used by the braid, null-cone and conjugation
  lanes.

They carry the same Zorn product with only a coordinate-name permutation:
`(a,b,x,y) ↔ (a,u,v,b)`.  The braid-side carrier intentionally uses explicit
`zornAdd`/`zornSmul` operations rather than native module instances, so this
module records an ordinary coordinate equivalence together with explicit
additive, scalar and product preservation theorems.

This is a carrier equivalence, not a physical particle identification.
-/

noncomputable section

namespace InfoGeometry.Physics.QCDCanonicalComplexZornBridge

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3
open InfoGeometry.Physics.SplitOctonionBraidSU3
open InfoGeometry.Physics.QCDFureyZornProjectorBridge
open InfoGeometry.Physics.QCDZornChargeConjugationBridge

abbrev CanonicalZorn := InfoGeometry.Canonical.ZornMatrix ℂ
abbrev ComplexZorn := InfoGeometry.Physics.SplitOctonionBraidSU3.Zorn

/-- Coordinate transport from the canonical Zorn matrix to the complex braid
carrier. -/
def canonicalToComplex (X : CanonicalZorn) : ComplexZorn :=
  { a := X.a, u := X.x, v := X.y, b := X.b }

/-- Coordinate transport back to the canonical carrier. -/
def complexToCanonical (X : ComplexZorn) : CanonicalZorn :=
  { a := X.a, b := X.b, x := X.u, y := X.v }

/-- The two complex Zorn coordinate carriers are equivalent as coordinate
spaces. Algebraic compatibility is proved separately below. -/
def canonicalComplexEquiv : CanonicalZorn ≃ ComplexZorn where
  toFun := canonicalToComplex
  invFun := complexToCanonical
  left_inv X := by
    ext i <;> rfl
  right_inv X := by
    apply zorn_ext <;> rfl

@[simp] theorem canonicalComplexEquiv_apply (X : CanonicalZorn) :
    canonicalComplexEquiv X = { a := X.a, u := X.x, v := X.y, b := X.b } := rfl

@[simp] theorem canonicalComplexEquiv_symm_apply (X : ComplexZorn) :
    canonicalComplexEquiv.symm X = { a := X.a, b := X.b, x := X.u, y := X.v } := rfl

/-- Additive compatibility with the explicit braid-side Zorn addition. -/
theorem canonicalComplexEquiv_add (X Y : CanonicalZorn) :
    canonicalComplexEquiv (X + Y) =
      zornAdd (canonicalComplexEquiv X) (canonicalComplexEquiv Y) := by
  apply zorn_ext
  · rfl
  · funext i; rfl
  · funext i; rfl
  · rfl

/-- Scalar compatibility with the explicit braid-side Zorn scalar operation. -/
theorem canonicalComplexEquiv_smul (c : ℂ) (X : CanonicalZorn) :
    canonicalComplexEquiv (c • X) =
      zornSmul c (canonicalComplexEquiv X) := by
  apply zorn_ext
  · rfl
  · funext i; rfl
  · funext i; rfl
  · rfl

/-- The canonical and complex dot products agree under the coordinate rename. -/
theorem canonical_dot_eq_dot3 (u v : Fin 3 → ℂ) :
    InfoGeometry.Canonical.ZornMatrix.dot u v = dot3 u v := by
  simp [InfoGeometry.Canonical.ZornMatrix.dot, dot3]

/-- The canonical and complex cross products agree under the coordinate rename. -/
theorem canonical_cross_eq_cross3 (u v : Fin 3 → ℂ) :
    InfoGeometry.Canonical.ZornMatrix.cross u v = cross3 u v := by
  funext i
  fin_cases i <;>
    simp [InfoGeometry.Canonical.ZornMatrix.cross, cross3]

/-- Exact preservation of the nonassociative Zorn product. -/
theorem canonicalComplexEquiv_mul (X Y : CanonicalZorn) :
    canonicalComplexEquiv (zMul X Y) =
      zornMul (canonicalComplexEquiv X) (canonicalComplexEquiv Y) := by
  apply zorn_ext
  · simp [canonicalComplexEquiv, canonicalToComplex, zMul, zornMul,
      canonical_dot_eq_dot3]
  · funext i
    simp [canonicalComplexEquiv, canonicalToComplex, zMul, zornMul,
      canonical_cross_eq_cross3]
  · funext i
    simp [canonicalComplexEquiv, canonicalToComplex, zMul, zornMul,
      canonical_cross_eq_cross3]
    ring
  · simp [canonicalComplexEquiv, canonicalToComplex, zMul, zornMul,
      canonical_dot_eq_dot3]
    ring

/-- The inverse transport also preserves the Zorn product. -/
theorem canonicalComplexEquiv_symm_mul (X Y : ComplexZorn) :
    canonicalComplexEquiv.symm (zornMul X Y) =
      zMul (canonicalComplexEquiv.symm X) (canonicalComplexEquiv.symm Y) := by
  apply canonicalComplexEquiv.injective
  simp only [Equiv.apply_symm_apply, canonicalComplexEquiv_mul]

/-- The canonical upper projector maps to the complex upper diagonal slot. -/
@[simp] theorem canonicalComplexEquiv_OP1 :
    canonicalComplexEquiv (OP1 : CanonicalZorn) = diagPlus := by
  apply zorn_ext <;> rfl

/-- The canonical lower projector maps to the complex lower diagonal slot. -/
@[simp] theorem canonicalComplexEquiv_OP2 :
    canonicalComplexEquiv (OP2 : CanonicalZorn) = diagMinus := by
  apply zorn_ext <;> rfl

/-- Canonical upper lanes map to pure complex upper lanes. -/
@[simp] theorem canonicalComplexEquiv_upperLane (u : ColorTriplet) :
    canonicalComplexEquiv (upperLane u) =
      ({ a := 0, u := u, v := 0, b := 0 } : ComplexZorn) := by
  apply zorn_ext <;> rfl

/-- Canonical lower lanes map to pure complex lower lanes. -/
@[simp] theorem canonicalComplexEquiv_lowerLane (v : ColorTriplet) :
    canonicalComplexEquiv (lowerLane v) =
      ({ a := 0, u := 0, v := v, b := 0 } : ComplexZorn) := by
  apply zorn_ext <;> rfl

/-- Transporting the native complex conjugation back to the canonical carrier. -/
def canonicalParticleConj (X : CanonicalZorn) : CanonicalZorn :=
  canonicalComplexEquiv.symm (particleConjZorn (canonicalComplexEquiv X))

@[simp] theorem canonicalParticleConj_sq (X : CanonicalZorn) :
    canonicalParticleConj (canonicalParticleConj X) = X := by
  apply canonicalComplexEquiv.injective
  change particleConjZorn (particleConjZorn (canonicalComplexEquiv X)) =
    canonicalComplexEquiv X
  exact particleConjZorn_sq _

@[simp] theorem canonicalParticleConj_OP1 :
    canonicalParticleConj (OP1 : CanonicalZorn) = OP2 := by
  apply canonicalComplexEquiv.injective
  change particleConjZorn diagPlus = diagMinus
  exact particleConjZorn_diagPlus

@[simp] theorem canonicalParticleConj_OP2 :
    canonicalParticleConj (OP2 : CanonicalZorn) = OP1 := by
  apply canonicalComplexEquiv.injective
  change particleConjZorn diagMinus = diagPlus
  exact particleConjZorn_diagMinus

/-- Consolidated carrier/product/conjugation transport packet. -/
theorem canonical_complex_zorn_packet :
    Function.Bijective canonicalComplexEquiv ∧
    (∀ X Y : CanonicalZorn,
      canonicalComplexEquiv (zMul X Y) =
        zornMul (canonicalComplexEquiv X) (canonicalComplexEquiv Y)) ∧
    (∀ c : ℂ, ∀ X : CanonicalZorn,
      canonicalComplexEquiv (c • X) =
        zornSmul c (canonicalComplexEquiv X)) ∧
    canonicalComplexEquiv (OP1 : CanonicalZorn) = diagPlus ∧
    canonicalComplexEquiv (OP2 : CanonicalZorn) = diagMinus ∧
    (∀ X : CanonicalZorn, canonicalParticleConj (canonicalParticleConj X) = X) :=
  ⟨canonicalComplexEquiv.bijective, canonicalComplexEquiv_mul,
    canonicalComplexEquiv_smul, canonicalComplexEquiv_OP1,
    canonicalComplexEquiv_OP2, canonicalParticleConj_sq⟩

end InfoGeometry.Physics.QCDCanonicalComplexZornBridge

end noncomputable section
