import InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge
import InfoGeometry.Canonical.SplitSpinorCARAlgebraBridge

/-!
# Twistor/exterior/spinor compatibility packet

This owner records the common finite exterior-algebra readout used by the
twistor--Plücker and split-spinor/CAR branches.  It deliberately does not
identify the four-component twistor carrier with the five-mode split-spinor
carrier; that comparison is a separate linear-equivalence theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.TwistorExteriorSpinorCompatibility

open InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge
open InfoGeometry.Canonical.SplitSpinorCARAlgebraBridge
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6

abbrev TwistorVector :=
  InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge.Vec4
abbrev TwistorBivector :=
  InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge.Plucker6

abbrev SpinorCarrier (R U : Type*) [CommRing R] [AddCommGroup U] [Module R U] :=
  Spinor R U

/-- The finite exterior/Plücker readout attached to an ordered twistor pair. -/
structure TwistorExteriorReadout where
  left : TwistorVector
  right : TwistorVector

def TwistorExteriorReadout.bivector (p : TwistorExteriorReadout) : TwistorBivector :=
  twistorLine p.left p.right

theorem TwistorExteriorReadout.bivector_eq (p : TwistorExteriorReadout) :
    p.bivector = twistorLine p.left p.right := by
  rfl

theorem TwistorExteriorReadout.on_klein (p : TwistorExteriorReadout) :
    Plucker6.kleinQ p.bivector = 0 := by
  rw [p.bivector_eq]
  exact twistorLine_on_klein p.left p.right

theorem TwistorExteriorReadout.swap (p : TwistorExteriorReadout) :
    twistorLine p.right p.left = pluckerNeg p.bivector := by
  rw [p.bivector_eq]
  exact twistorLine_swap p.left p.right

/-- The spinor-side finite exterior readout attached to two dual generators. -/
structure SpinorExteriorReadout {R U : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] where
  alpha : Module.Dual R U
  beta : Module.Dual R U

theorem SpinorExteriorReadout.creation_nilpotent
    {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    (p : SpinorExteriorReadout (R := R) (U := U)) :
    creation p.alpha * creation p.alpha = 0 := by
  exact SplitSpinorCARAlgebraBridge.creation_sq_zero p.alpha

theorem SpinorExteriorReadout.creation_anticomm
    {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    (p : SpinorExteriorReadout (R := R) (U := U)) :
    creation p.alpha * creation p.beta + creation p.beta * creation p.alpha = 0 := by
  exact SplitSpinorCARAlgebraBridge.creation_anticomm p.alpha p.beta

/-!
The compatibility content is the conjunction of the two finite readouts:
decomposability/Klein-nullity on the twistor side and CAR nilpotency on the
spinor side.  No identification of their carriers is assumed here.
-/
theorem exterior_readout_compatibility
    (p : TwistorExteriorReadout)
    {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    (q : SpinorExteriorReadout (R := R) (U := U)) :
    Plucker6.kleinQ p.bivector = 0 ∧
      creation q.alpha * creation q.alpha = 0 ∧
      creation q.alpha * creation q.beta + creation q.beta * creation q.alpha = 0 := by
  exact ⟨p.on_klein, q.creation_nilpotent, q.creation_anticomm⟩

end InfoGeometry.Canonical.TwistorExteriorSpinorCompatibility
