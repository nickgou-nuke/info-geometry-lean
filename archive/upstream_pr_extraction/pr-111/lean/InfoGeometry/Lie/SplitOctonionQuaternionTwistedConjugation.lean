import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
import InfoGeometry.Algebra.Zorn.CanonicalConjugation

set_option autoImplicit false

/-!
# Twisted conjugation in quaternionic `(4+4)` coordinates

The native split-octonion conjugation is transported through the existing
quaternion-pair/Zorn linear equivalence.  On Cartesian coordinates it is
ordinary quaternion conjugation on the first copy and full negation on the
second copy.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation

open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

/-- Cartesian expression of split-octonion conjugation:
`(q, r) ↦ (quaternionConj q, -r)`. -/
def cartesianTwistedConj :
    CartesianCoordinates →ₗ[ℝ] CartesianCoordinates where
  toFun qr := ((qr.1.1, -qr.1.2), (-qr.2.1, -qr.2.2))
  map_add' X Y := by
    apply Prod.ext <;> apply Prod.ext <;> simp [add_comm]
  map_smul' c X := by
    apply Prod.ext <;> apply Prod.ext <;> simp

@[simp] theorem cartesianTwistedConj_apply (qr : CartesianCoordinates) :
    cartesianTwistedConj qr =
      ((qr.1.1, -qr.1.2), (-qr.2.1, -qr.2.2)) :=
  rfl

/-- The quaternion-pair formula is exactly the native canonical Zorn
conjugation, not a new involution on the split-octonion algebra. -/
theorem cartesianZorn_intertwines_twistedConj (qr : CartesianCoordinates) :
    cartesianZornLinearEquiv (cartesianTwistedConj qr) =
      canonicalConj (cartesianZornLinearEquiv qr) := by
  apply canonicalVectorEquiv.injective
  ext i <;>
    simp [cartesianTwistedConj, canonicalConj, canonicalVectorEquiv,
      InfoGeometry.Algebra.ZornVectorMatrix.conj] <;>
    ring

/-- The transported twisted conjugation is an involution. -/
@[simp] theorem cartesianTwistedConj_involutive (qr : CartesianCoordinates) :
    cartesianTwistedConj (cartesianTwistedConj qr) = qr := by
  apply Prod.ext <;> apply Prod.ext <;> simp

/-- Twisted conjugation preserves the split `(4,4)` quadratic form expressed
as the difference of the two Euclidean quaternion norms. -/
theorem cartesianTwistedConj_preserves_normDifference
    (qr : CartesianCoordinates) :
    quaternionNorm (cartesianTwistedConj qr).1 -
        quaternionNorm (cartesianTwistedConj qr).2 =
      quaternionNorm qr.1 - quaternionNorm qr.2 := by
  rcases qr with ⟨⟨q0, q⟩, ⟨r0, r⟩⟩
  simp [cartesianTwistedConj, quaternionNorm,
    InfoGeometry.Canonical.ZornMatrix.dot]

/-- Conjugation exchanges the two scalar circular sheets. -/
@[simp] theorem cartesianTwistedConj_scalarPlus :
    cartesianTwistedConj scalarPlus = scalarMinus := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp [cartesianTwistedConj, scalarPlus, scalarMinus,
      quaternionScalar, ellScalar]

@[simp] theorem cartesianTwistedConj_scalarMinus :
    cartesianTwistedConj scalarMinus = scalarPlus := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp [cartesianTwistedConj, scalarPlus, scalarMinus,
      quaternionScalar, ellScalar]

/-- Each of the three positive/negative circular null channels is negated. -/
@[simp] theorem cartesianTwistedConj_rootPlus (i : Fin 3) :
    cartesianTwistedConj (rootPlus i) = -rootPlus i := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp [rootPlus, cartesianTwistedConj, quaternionAxis, ellAxis]

@[simp] theorem cartesianTwistedConj_rootMinus (i : Fin 3) :
    cartesianTwistedConj (rootMinus i) = -rootMinus i := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp [rootMinus, cartesianTwistedConj, quaternionAxis, ellAxis]

/-- Native canonical Zorn conjugation bundled as a real-linear map. -/
def canonicalConjLinear :
    SplitOctonionQuaternionZornCoordinates.CZ →ₗ[ℝ]
      SplitOctonionQuaternionZornCoordinates.CZ where
  toFun := canonicalConj
  map_add' := canonicalConj_add
  map_smul' := canonicalConj_smul

/-- Bundled conjugacy of the two linear involutions. -/
theorem cartesianZorn_twistedConj_conjugacy :
    cartesianZornLinearEquiv.toLinearMap.comp cartesianTwistedConj =
      canonicalConjLinear.comp cartesianZornLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro qr
  exact cartesianZorn_intertwines_twistedConj qr

end InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation
