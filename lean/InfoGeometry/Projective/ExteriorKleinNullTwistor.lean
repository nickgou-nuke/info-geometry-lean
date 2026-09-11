import InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.NullProjective

/-!
# The exterior Klein locus as a projective null twistor space

This owner packages the existing Klein polynomial on `⋀² ℝ⁴` as a native
Mathlib `QuadraticForm`.  It then identifies the existing projective Klein
locus with the projective null space of that form and composes this with the
already proved set-level Plücker equivalence for real two-planes.

This is a real exterior-square null-twistor bridge.  It does not identify this
carrier with the complex Penrose twistor representation.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Projective.ExteriorKleinNullTwistor

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv
open InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient

/-- The coordinate Klein quadratic form
`p01*p23 - p02*p13 + p03*p12` on six Plücker coordinates. -/
def coordinateKleinQuadraticForm : QuadraticForm ℝ (Fin 6 → ℝ) :=
  QuadraticMap.ofPolar
    (fun p => p 0 * p 5 - p 1 * p 4 + p 2 * p 3)
    (fun a p => by simp; ring)
    (fun p p' q => by dsimp [QuadraticMap.polar]; ring)
    (fun a p q => by dsimp [QuadraticMap.polar]; ring)

/-- The native quadratic form on the literal exterior square, transported
through the existing exterior/bivector and bivector/coordinate equivalences. -/
def exteriorKleinQuadraticForm : QuadraticForm ℝ ExteriorSquare :=
  coordinateKleinQuadraticForm.comp
    (bivector4CoordinateLinearEquiv.toLinearMap.comp
      exteriorBivectorLinearEquiv.toLinearMap)

@[simp] theorem exteriorKleinQuadraticForm_apply (X : ExteriorSquare) :
    exteriorKleinQuadraticForm X = exteriorKleinForm X := by
  change coordinateKleinQuadraticForm
      (bivector4CoordinateLinearEquiv (exteriorBivectorLinearEquiv X)) = _
  simp [coordinateKleinQuadraticForm, exteriorKleinForm, kleinForm]

/-- The existing projective Klein predicate is literally the projective null
predicate of the transported exterior-square quadratic form. -/
theorem isKlein_iff_isNull (p : ℙ ℝ ExteriorSquare) :
    IsKlein p ↔
      InfoGeometry.Twistor.IsNull exteriorKleinQuadraticForm p := by
  refine Projectivization.ind (p := p) ?_
  intro X hX
  rw [isKlein_mk_iff, InfoGeometry.Twistor.isNull_mk_iff,
    exteriorKleinQuadraticForm_apply]

/-- The projective Klein locus and the null twistor space of the native
exterior Klein quadratic form are the same projective rays. -/
def kleinLocusEquivTwistorSpace :
    KleinLocus ≃
      InfoGeometry.Twistor.TwistorSpace exteriorKleinQuadraticForm where
  toFun p := ⟨p.1, (isKlein_iff_isNull p.1).1 p.2⟩
  invFun p := ⟨p.1, (isKlein_iff_isNull p.1).2 p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

@[simp] theorem kleinLocusEquivTwistorSpace_val (p : KleinLocus) :
    (kleinLocusEquivTwistorSpace p).1 = p.1 :=
  rfl

/-- Set-level real two-planes in `ℝ⁴` are exactly the projective null rays
of the native exterior Klein quadratic form. -/
def realTwoPlaneEquivTwistorSpace :
    RealTwoPlane ≃
      InfoGeometry.Twistor.TwistorSpace exteriorKleinQuadraticForm :=
  realTwoPlaneEquivKleinLocus.trans kleinLocusEquivTwistorSpace

end InfoGeometry.Projective.ExteriorKleinNullTwistor
