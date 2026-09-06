import InfoGeometry.Canonical.KleinPresentedGroup
import InfoGeometry.Canonical.KleinBottleTwistedCommutantBridge
import InfoGeometry.Canonical.KleinMonodromyRepresentationSpace

/-!
# Klein-bottle representation from a twisted unit pair

This consumer joins the existing quotient presentation to the existing
twisted-commutant API.  A unit `U` that implements an involution on an
embedded element `i v`, together with a unit `V` representing that element,
produces the native group homomorphism from the presented Klein group.

No crossed-product C*-algebra, Hilbert completion, or Tomita identification
is introduced here.
-/

namespace InfoGeometry.Canonical.KleinBottleTwistedRepresentationBridge

open InfoGeometry.Canonical.KleinPresentedGroup
open InfoGeometry.Canonical.KleinBottleTwistedCommutant
open InfoGeometry.Canonical.KleinMonodromyRepresentationSpace

variable {A B : Type*} [Ring A] [Ring B]

/-- The twisted normalizer relation becomes the Klein relation when the
involuted algebra element is represented by the inverse unit. -/
theorem twisted_unit_inverts_embedded_element
    (i : A →+* B) (U : Units B) (α : KleinInvolution A) (v : Units A)
    (hU : IsTwistedCommutant i α.toRingAut (U : B))
    (hα : α.toRingAut (v : A) = (↑(v⁻¹) : A)) :
    (U : B) * (↑(Units.map i.toMonoidHom v) : B) * (↑(U⁻¹) : B) =
      (↑((Units.map i.toMonoidHom v)⁻¹) : B) := by
  calc
    (U : B) * (↑(Units.map i.toMonoidHom v) : B) * (↑(U⁻¹) : B) =
        (U : B) * i (v : A) * (↑(U⁻¹) : B) := by rfl
    _ = i (α.toRingAut (v : A)) :=
      twisted_unit_conjugates i U α hU (v : A)
    _ = i (↑(v⁻¹) : A) := by rw [hα]
    _ = (↑(Units.map i.toMonoidHom (v⁻¹)) : B) := by rfl
    _ = (↑((Units.map i.toMonoidHom v)⁻¹) : B) := by simp

/-- The native quotient-group representation induced by a twisted unit pair. -/
def kleinUnitsRep
    (i : A →+* B) (U : Units B) (α : KleinInvolution A) (v : Units A)
    (hU : IsTwistedCommutant i α.toRingAut (U : B))
    (hα : α.toRingAut (v : A) = (↑(v⁻¹) : A)) :
    KleinGroup →* Units B :=
  kleinRep U (Units.map i.toMonoidHom v) (by
    apply Units.ext
    exact twisted_unit_inverts_embedded_element i U α v hU hα)

/-- The representation sends the two presented generators to the chosen
twisted and transverse units. -/
theorem kleinUnitsRep_generators
    (i : A →+* B) (U : Units B) (α : KleinInvolution A) (v : Units A)
    (hU : IsTwistedCommutant i α.toRingAut (U : B))
    (hα : α.toRingAut (v : A) = (↑(v⁻¹) : A)) :
    kleinUnitsRep i U α v hU hα (toKlein genA) = U ∧
    kleinUnitsRep i U α v hU hα (toKlein genB) = Units.map i.toMonoidHom v := by
  exact kleinRep_relator_relation U (Units.map i.toMonoidHom v) (by
    apply Units.ext
    exact twisted_unit_inverts_embedded_element i U α v hU hα)

theorem kleinUnitsRep_generator_relation
    (i : A →+* B) (U : Units B) (α : KleinInvolution A) (v : Units A)
    (hU : IsTwistedCommutant i α.toRingAut (U : B))
    (hα : α.toRingAut (v : A) = (↑(v⁻¹) : A)) :
    kleinUnitsRep i U α v hU hα (toKlein genA) *
        kleinUnitsRep i U α v hU hα (toKlein genB) *
        (kleinUnitsRep i U α v hU hα (toKlein genA))⁻¹ =
      (kleinUnitsRep i U α v hU hα (toKlein genB))⁻¹ := by
  have hg := kleinUnitsRep_generators i U α v hU hα
  rw [hg.1, hg.2]
  apply Units.ext
  exact twisted_unit_inverts_embedded_element i U α v hU hα

/-- Package the represented generators as the native relation subtype used by
the monodromy-space owner. -/
def kleinUnitsMonodromyPair
    (i : A →+* B) (U : Units B) (α : KleinInvolution A) (v : Units A)
    (hU : IsTwistedCommutant i α.toRingAut (U : B))
    (hα : α.toRingAut (v : A) = (↑(v⁻¹) : A)) :
    KleinMonodromyPair (Units B) :=
  ⟨(kleinUnitsRep i U α v hU hα (toKlein genA),
      kleinUnitsRep i U α v hU hα (toKlein genB)),
    kleinUnitsRep_generator_relation i U α v hU hα⟩

/-! The orientation-reversing generator acts by inversion on the transverse
generator, so its even winding returns to the ordinary commutant relation. -/

theorem kleinUnitsRep_even_winding_commutes
    (i : A →+* B) (U : Units B) (α : KleinInvolution A) (v : Units A)
    (hU : IsTwistedCommutant i α.toRingAut (U : B))
    (hα : α.toRingAut (v : A) = (↑(v⁻¹) : A)) :
    (kleinUnitsRep i U α v hU hα (toKlein genA) *
        kleinUnitsRep i U α v hU hα (toKlein genA)) *
        kleinUnitsRep i U α v hU hα (toKlein genB) =
      kleinUnitsRep i U α v hU hα (toKlein genB) *
        (kleinUnitsRep i U α v hU hα (toKlein genA) *
          kleinUnitsRep i U α v hU hα (toKlein genA)) := by
  simpa only [map_mul] using congrArg (kleinUnitsRep i U α v hU hα)
    klein_glide_square_commutes_with_transverse

end InfoGeometry.Canonical.KleinBottleTwistedRepresentationBridge
