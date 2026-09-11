import InfoGeometry.Projective.ExteriorKleinNullTwistor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.ExteriorKleinCoordinateIncidence
import InfoGeometry.Twistor.ProjectiveNullPolarIncidence

/-!
# Polar incidence on the exterior Klein null twistor space

The polar form of the native exterior Klein quadratic form is identified with
the established six-coordinate Klein incidence pairing.  Consequently polar
incidence of projective null rays is exactly nontrivial intersection of the
corresponding real two-planes.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Projective.ExteriorKleinNullTwistorIncidence

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Projective.ExteriorKleinProjective
open InfoGeometry.Projective.ExteriorKleinFrameSurjection
open InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv
open InfoGeometry.Projective.ExteriorKleinTwoPlaneIncidence
open InfoGeometry.Projective.ExteriorKleinCoordinateIncidence
open InfoGeometry.Projective.ExteriorKleinNullTwistor
open InfoGeometry.Twistor.ProjectiveNullPolarIncidence

/-- The polar form of the transported exterior quadratic form is the standard
mixed Klein pairing in native bivector coordinates. -/
theorem exteriorKleinQuadraticForm_polar (X Y : ExteriorSquare) :
    QuadraticMap.polar exteriorKleinQuadraticForm X Y =
      (exteriorBivectorLinearEquiv X).p01 *
          (exteriorBivectorLinearEquiv Y).p23 +
        (exteriorBivectorLinearEquiv Y).p01 *
          (exteriorBivectorLinearEquiv X).p23 -
        (exteriorBivectorLinearEquiv X).p02 *
          (exteriorBivectorLinearEquiv Y).p13 -
        (exteriorBivectorLinearEquiv Y).p02 *
          (exteriorBivectorLinearEquiv X).p13 +
        (exteriorBivectorLinearEquiv X).p03 *
          (exteriorBivectorLinearEquiv Y).p12 +
        (exteriorBivectorLinearEquiv Y).p03 *
          (exteriorBivectorLinearEquiv X).p12 := by
  unfold QuadraticMap.polar
  unfold exteriorKleinQuadraticForm
  rw [QuadraticMap.comp_apply, QuadraticMap.comp_apply,
    QuadraticMap.comp_apply, map_add]
  simp [coordinateKleinQuadraticForm]
  ring_nf

/-- On nondegenerate frame representatives, projective polar incidence is
exactly the already established Klein/plane incidence relation. -/
theorem polarIncident_frame_iff_kleinIncident
    (uv st : NondegenerateExteriorFrame) :
    PolarIncident exteriorKleinQuadraticForm
        (Projectivization.mk ℝ (exteriorPower.ιMulti ℝ 2 uv.1) uv.2)
        (Projectivization.mk ℝ (exteriorPower.ιMulti ℝ 2 st.1) st.2) ↔
      KleinIncident (frameToKleinLocus uv) (frameToKleinLocus st) := by
  rw [polarIncident_mk_iff, exteriorKleinQuadraticForm_polar,
    kleinIncident_iff_coordinate_incidence]
  have huv : uv.1 = ![uv.1 0, uv.1 1] := by
    funext i
    fin_cases i <;> rfl
  have hst : st.1 = ![st.1 0, st.1 1] := by
    funext i
    fin_cases i <;> rfl
  rw [huv, hst]
  rw [exteriorBivectorLinearEquiv_ιMulti_eq_alternating,
    exteriorBivectorLinearEquiv_ιMulti_eq_alternating]
  simp [wedgeVec4Alternating_apply, wedgeVec4,
    InfoGeometry.Projective.KleinQuadricIncidence.Plucker6.incidenceForm,
    linePlucker]
  ring_nf

/-- For arbitrary projective Klein rays, native quadratic polar incidence and
intrinsic two-plane incidence coincide. -/
theorem polarIncident_iff_kleinIncident (p q : KleinLocus) :
    PolarIncident exteriorKleinQuadraticForm p.1 q.1 ↔
      KleinIncident p q := by
  obtain ⟨uv, rfl⟩ := frameToKleinLocus_surjective p
  obtain ⟨st, rfl⟩ := frameToKleinLocus_surjective q
  exact polarIncident_frame_iff_kleinIncident uv st

/-- Intrinsic polar incidence on the exterior projective-null twistor space is
exactly nontrivial intersection of the corresponding real two-planes. -/
theorem nullPolarIncident_iff_planesIncident
    (p q : InfoGeometry.Twistor.TwistorSpace exteriorKleinQuadraticForm) :
    NullPolarIncident exteriorKleinQuadraticForm p q ↔
      PlanesIncident (realTwoPlaneEquivTwistorSpace.symm p)
        (realTwoPlaneEquivTwistorSpace.symm q) := by
  change PolarIncident exteriorKleinQuadraticForm p.1 q.1 ↔ _
  let kp := kleinLocusEquivTwistorSpace.symm p
  let kq := kleinLocusEquivTwistorSpace.symm q
  change PolarIncident exteriorKleinQuadraticForm kp.1 kq.1 ↔
    PlanesIncident ((realTwoPlaneEquivKleinLocus).symm kp)
      ((realTwoPlaneEquivKleinLocus).symm kq)
  rw [polarIncident_iff_kleinIncident]
  rfl

end InfoGeometry.Projective.ExteriorKleinNullTwistorIncidence
