import InfoGeometry.Clifford.Soldering
import InfoGeometry.Twistor.Incidence
import InfoGeometry.Projective.Twistor.Incidence
import InfoGeometry.Projective.ArnoldRelations
import InfoGeometry.Projective.NonIsoConf3RankIngestion
import InfoGeometry.Projective.ExteriorKleinNullTwistor
import InfoGeometry.Projective.ExteriorKleinTwoPlaneIncidence
import InfoGeometry.Projective.ExteriorKleinNullTwistorIncidence
import InfoGeometry.Topology.RohozhkinDelaunayBraiding
/-!
# Twistor / Amplituhedron Bridge

This module records the theorem-safe corridor between the existing
Klein-quadric, twistor-incidence, `Conf₃`, and Rohozhkin/Delaunay layers.

It intentionally does not prove that the non-isotropic `Conf₃` complement is an
amplituhedron, does not identify its rank arithmetic with an `N = 4` SYM
supermultiplet, and does not derive BCFW recursion or plabic-graph moves from
the Arnold/cooperad surface.  Those are comparison theorems to be supplied by a
separate amplituhedron owner.

#### BUCKET 1: CLOSED FINITE THEOREMS
- `common_twistor_incidence_forces_null_boundary`: re-exports the classical
  twistor-incidence null-separation theorem.
- `penrose_projective_null_twistor_readout`: re-exports inhabitedness of the
  Penrose projective null twistor space.
- `candidate_conf3_spin_tiled_rank32_readout`: re-exports the existing finite
  candidate rank arithmetic.
- `rohozhkin_pentagon_face_identity_readout`: re-exports the rational Appendix
  A pentagon identity.
- `arnold_mixed_relation_kernel_readout`: re-exports the finite Arnold mixed
  relation kernel-annihilation theorem.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
No conditional theorem is exported here until an explicit comparison carries
mathematical content beyond returning its own equality hypothesis.

#### BUCKET 3: OPEN CLOSURE DEBT
- Formalize the Grassmannian/Klein-quadric line correspondence used by
  projective twistor theory.
- Formalize positive Grassmannian / amplituhedron cells and their boundaries.
- Prove any comparison between Arnold/cooperad relations and BCFW recursion.
- Prove any comparison between Rohozhkin/Delaunay flips and plabic graph moves.
- Replace the candidate `Conf₃` rank fixture by an independently audited
  D-module/Singular property if the project needs a final rank theorem.
-/

namespace InfoGeometry.Projective.TwistorAmplituhedronBridge

open InfoGeometry.Clifford.Soldering
open InfoGeometry.Twistor.Incidence
open InfoGeometry.Projective.Twistor
open InfoGeometry.Projective.ArnoldRelations
open InfoGeometry.Projective.NonIsoConf3RankIngestion
open InfoGeometry.Projective.ExteriorKleinNullTwistor
open InfoGeometry.Projective.ExteriorKleinFrameSurjection
open InfoGeometry.Projective.ExteriorKleinTwoPlaneIncidence
open InfoGeometry.Projective.ExteriorKleinTwoPlaneEquiv
open InfoGeometry.Projective.ExteriorKleinTwoPlaneQuotient
open InfoGeometry.Projective.ExteriorKleinNullTwistorIncidence
open InfoGeometry.Twistor.ProjectiveNullPolarIncidence
open InfoGeometry.Topology.RohozhkinDelaunayBraiding
open InfoGeometry.Topology.Delaunay

/--
If two spacetime points are incident with the same twistor whose primary spinor
is nonzero, their separation lies on the light cone.

This is the exact local bridge needed before interpreting line intersection in
twistor space as a lightlike boundary event.
-/
theorem common_twistor_incidence_forces_null_boundary
    (Z : Twistor) (X Y : Vec22)
    (hX : Incident Z X) (hY : Incident Z Y) (hPi : Z.2 ≠ 0) :
    q22 (X - Y) = 0 :=
  incident_points_null_separated Z X Y hX hY hPi

/- The Penrose projective null twistor owner exposes a concrete point. -/
noncomputable abbrev penrose_projective_null_twistor_point :
    PenroseProjectiveNullTwistor :=
  penroseProjectiveNullTwistor

theorem penrose_projective_null_twistor_readout :
    Nonempty PenroseProjectiveNullTwistor :=
  ⟨penrose_projective_null_twistor_point⟩

/-- The exterior Plücker/Klein construction factors through the native
projective null-twistor carrier on every nondegenerate frame.  This is a real
exterior-square readout; it does not identify that carrier with complex
Penrose twistors. -/
theorem exteriorKlein_nullTwistor_frame_readout
    (uv : NondegenerateExteriorFrame) :
    realTwoPlaneEquivTwistorSpace (frameSpan uv) =
      kleinLocusEquivTwistorSpace (frameToKleinLocus uv) := by
  change kleinLocusEquivTwistorSpace
      (realTwoPlaneEquivKleinLocus (frameSpan uv)) = _
  rw [realTwoPlaneEquivKleinLocus_frameSpan]

/-- Polar incidence of the transported exterior null-twistors is exactly the
vanishing of the top exterior product of the two frame representatives. -/
theorem exteriorKlein_nullTwistor_incidence_readout
    (uv st : NondegenerateExteriorFrame) :
    NullPolarIncident exteriorKleinQuadraticForm
        (kleinLocusEquivTwistorSpace (frameToKleinLocus uv))
        (kleinLocusEquivTwistorSpace (frameToKleinLocus st)) ↔
      exteriorPower.ιMulti ℝ 4 (combinedFrame uv st) = 0 := by
  change PolarIncident exteriorKleinQuadraticForm
      (Projectivization.mk ℝ (exteriorPower.ιMulti ℝ 2 uv.1) uv.2)
      (Projectivization.mk ℝ (exteriorPower.ιMulti ℝ 2 st.1) st.2) ↔ _
  rw [polarIncident_frame_iff_kleinIncident,
    kleinIncident_frameToKleinLocus_iff_wedge_eq_zero]

/--
Readout of the existing candidate `Conf₃` spin-tiled rank arithmetic.

This is still the candidate fixture from `NonIsoConf3RankIngestion`, not a
property external D-module computation.
-/
theorem candidate_conf3_spin_tiled_rank32_readout :
    candidateLocalBettiData.totalRank *
      InfoGeometry.Projective.PenroseSpinTiling.spinTilingMultiplicity = 32 :=
  candidateLocalBettiData_spinTiled_rank32

/-- The Rohozhkin Appendix A five-flip rational pentagon block evaluates to `1`. -/
theorem rohozhkin_pentagon_face_identity_readout
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    rohozhkinMatrix
        (appendixPentagonWord zi zj zk zl zm) =
      (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ) :=
  appendixPentagonWord_matrix_eq_one zi zj zk zl zm
    h_il h_ik h_km h_jm h_jl

/--
Finite Arnold readout: if a target model's kernel contains the abstract
three-point mixed relation, that target model kills the relation.

This is not yet a theorem about concrete `d log Q` forms on `F_Q(C^4,3)`.
-/
theorem arnold_mixed_relation_kernel_readout
    (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    {A : Type*} [Semiring A]
    (w12 w23 w31 : ArnoldExterior R M)
    (φ : ArnoldExterior R M →+* A)
    (hKer : arnoldMixedRelation R M w12 w23 w31 ∈ RingHom.ker φ) :
    φ (arnoldMixedRelation R M w12 w23 w31) = 0 :=
  arnold_mixed_relation_vanishes_under_kernel_membership
    R M w12 w23 w31 φ hKer

end InfoGeometry.Projective.TwistorAmplituhedronBridge
