import InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.ExteriorKleinTwistorIncidence

/-!
# Exterior Klein incidence for native twistor lines

The projective exterior lane identifies incidence of real two-planes with the
Klein polar equation.  This owner states that result using the actual
`twistorLine` declaration owned by `ExteriorGrassmannianTwistorBridge`.

No new twistor, Grassmannian, or Pluecker carrier is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExteriorKleinTwistorLineIncidence

open InfoGeometry.Projective.ExteriorKleinFrameSurjection
open InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient
open InfoGeometry.Projective.ExteriorKleinTwoPlaneIncidence
open InfoGeometry.Projective.ExteriorKleinTwistorIncidence

/-- The coordinate-free incidence of two real planes is exactly the polar
incidence of their native twistor lines. -/
theorem kleinIncident_iff_twistorLine_kleinPolar
    (uv st : NondegenerateExteriorFrame) :
    KleinIncident (frameToKleinLocus uv) (frameToKleinLocus st) ↔
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinPolar
        (InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge.twistorLine
          (twistorCoordinateVec4 (uv.1 0))
          (twistorCoordinateVec4 (uv.1 1)))
        (InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge.twistorLine
          (twistorCoordinateVec4 (st.1 0))
          (twistorCoordinateVec4 (st.1 1))) = 0 := by
  simpa [InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge.twistorLine] using
    kleinIncident_iff_twistor_kleinPolar uv st

/-- Intrinsic incidence of the two planes spanned by concrete frames is the
polar incidence of their native twistor-line coordinates. -/
theorem planesIncident_frameSpan_iff_twistorLine_kleinPolar
    (uv st : NondegenerateExteriorFrame) :
    PlanesIncident (frameSpan uv) (frameSpan st) ↔
      InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinPolar
        (InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge.twistorLine
          (twistorCoordinateVec4 (uv.1 0))
          (twistorCoordinateVec4 (uv.1 1)))
        (InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge.twistorLine
          (twistorCoordinateVec4 (st.1 0))
          (twistorCoordinateVec4 (st.1 1))) = 0 := by
  rw [← combinedFrame_wedge_eq_zero_iff_incident,
    ← kleinIncident_frameToKleinLocus_iff_wedge_eq_zero,
    kleinIncident_iff_twistorLine_kleinPolar]

/-- Frame-independent set-level `Gr(2,4)` incidence readout.  Frames occur
only as coordinate witnesses for the two intrinsic real planes. -/
theorem planesIncident_iff_exists_twistorLine_kleinPolar
    (P Q : RealTwoPlane) :
    PlanesIncident P Q ↔
      ∃ uv st : NondegenerateExteriorFrame,
        frameSpan uv = P ∧ frameSpan st = Q ∧
          InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinPolar
            (InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge.twistorLine
              (twistorCoordinateVec4 (uv.1 0))
              (twistorCoordinateVec4 (uv.1 1)))
            (InfoGeometry.Canonical.ExteriorGrassmannianTwistorBridge.twistorLine
              (twistorCoordinateVec4 (st.1 0))
              (twistorCoordinateVec4 (st.1 1))) = 0 := by
  constructor
  · intro hPQ
    obtain ⟨uv, huv⟩ := frameSpan_surjective P
    obtain ⟨st, hst⟩ := frameSpan_surjective Q
    refine ⟨uv, st, huv, hst, ?_⟩
    apply (planesIncident_frameSpan_iff_twistorLine_kleinPolar uv st).1
    simpa [huv, hst] using hPQ
  · rintro ⟨uv, st, huv, hst, hpolar⟩
    have hinc : PlanesIncident (frameSpan uv) (frameSpan st) :=
      (planesIncident_frameSpan_iff_twistorLine_kleinPolar uv st).2 hpolar
    simpa [huv, hst] using hinc

end InfoGeometry.Canonical.ExteriorKleinTwistorLineIncidence
