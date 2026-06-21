import InfoGeometry.Twistor.Incidence
import InfoGeometry.Projective.NonIsoConf3RankIngestion
import InfoGeometry.Projective.RohozhkinDelaunayBraiding

/-!
# Twistor / Amplituhedron Boundary Interface

This file records the theorem-safe part of the requested dictionary:

* classical twistor incidence forces null separation;
* therefore a non-isotropic pair cannot share a common twistor with nonzero
  primary spinor;
* the current rank-32 surface is the explicit `NonIsoConf3RankIngestion`
  candidate arithmetic;
* the Rohozhkin/Delaunay contribution is the rational pentagon/pure-braid
  boundary already owned by the topology/projective Rohozhkin files.

It does not prove an amplituhedron theorem, BCFW recursion, a plabic graph
equivalence, `N=4` SYM state counting, or a physical scattering interpretation.
Those remain explicit comparison data to be supplied by future owner files.
-/

namespace InfoGeometry.Projective.TwistorAmplituhedronBoundary

open InfoGeometry.Clifford.Soldering
open InfoGeometry.Twistor.Incidence
open InfoGeometry.Projective.NonIsoConf3RankIngestion
open InfoGeometry.Projective.PenroseSpinTiling

/-- Pairwise non-null condition for three points in the real `2 x 2` soldered model. -/
def TripleNonNull (X₁ X₂ X₃ : Vec22) : Prop :=
  q22 (X₁ - X₂) ≠ 0 ∧ q22 (X₂ - X₃) ≠ 0 ∧ q22 (X₃ - X₁) ≠ 0

/--
If two points share a common incident twistor with nonzero primary spinor, their
difference is null.
-/
theorem common_twistor_incidence_forces_null
    (Z : Twistor) (X Y : Vec22)
    (hX : Incident Z X) (hY : Incident Z Y) (hπ : Z.2 ≠ 0) :
    q22 (X - Y) = 0 :=
  incident_points_null_separated Z X Y hX hY hπ

/--
Contrapositive twistor readout: a non-null pair cannot be represented by a
single common incident twistor with nonzero primary spinor.
-/
theorem non_null_pair_excludes_common_twistor
    (X Y : Vec22) (hXY : q22 (X - Y) ≠ 0) :
    ¬ ∃ Z : Twistor, Incident Z X ∧ Incident Z Y ∧ Z.2 ≠ 0 := by
  rintro ⟨Z, hX, hY, hπ⟩
  exact hXY (common_twistor_incidence_forces_null Z X Y hX hY hπ)

/--
Triple non-isotropic configuration readout: each pair excludes a common
nonzero-spinor incidence twistor.
-/
theorem triple_nonnull_excludes_pairwise_common_twistors
    (X₁ X₂ X₃ : Vec22) (h : TripleNonNull X₁ X₂ X₃) :
    (¬ ∃ Z : Twistor, Incident Z X₁ ∧ Incident Z X₂ ∧ Z.2 ≠ 0) ∧
      (¬ ∃ Z : Twistor, Incident Z X₂ ∧ Incident Z X₃ ∧ Z.2 ≠ 0) ∧
      (¬ ∃ Z : Twistor, Incident Z X₃ ∧ Incident Z X₁ ∧ Z.2 ≠ 0) := by
  exact ⟨non_null_pair_excludes_common_twistor X₁ X₂ h.1,
    non_null_pair_excludes_common_twistor X₂ X₃ h.2.1,
    non_null_pair_excludes_common_twistor X₃ X₁ h.2.2⟩

/--
Amplituhedron/BCFW comparison boundary.

The maps are deliberately explicit data.  Supplying this structure is the future
owner obligation for connecting null-pair boundary limits to any chosen
amplituhedron or on-shell diagram formalization.
-/
structure AmplituhedronBoundarySpec where
  Boundary : Type
  boundaryOfNullPair : ∀ X Y : Vec22, q22 (X - Y) = 0 → Boundary
  bcfwComparison : Prop
  rohozhkinComparison : Prop

namespace AmplituhedronBoundarySpec

/--
Given a boundary comparison spec, common twistor incidence produces a boundary
point through the supplied null-pair map.
-/
def boundary_of_common_twistor
    (S : AmplituhedronBoundarySpec)
    (Z : Twistor) (X Y : Vec22)
    (hX : Incident Z X) (hY : Incident Z Y) (hπ : Z.2 ≠ 0) :
    S.Boundary :=
  S.boundaryOfNullPair X Y
    (common_twistor_incidence_forces_null Z X Y hX hY hπ)

/-- Read back the BCFW comparison as an explicit assumption of the spec. -/
theorem bcfwComparison_readback (S : AmplituhedronBoundarySpec)
    (h : S.bcfwComparison) :
    S.bcfwComparison :=
  h

/-- Read back the Rohozhkin/plabic comparison as an explicit assumption of the spec. -/
theorem rohozhkinComparison_readback (S : AmplituhedronBoundarySpec)
    (h : S.rohozhkinComparison) :
    S.rohozhkinComparison :=
  h

end AmplituhedronBoundarySpec

/--
Rank-32 readout currently available for the triple non-isotropic lane.

This is the candidate arithmetic from `NonIsoConf3RankIngestion`; it is not an
independent proof of the external D-module/de Rham computation.
-/
theorem candidate_conf3_spin_tiled_rank32 :
    candidateLocalBettiData.totalRank * spinTilingMultiplicity = 32 :=
  candidateLocalBettiData_spinTiled_rank32

/--
Conditional readout from arbitrary externally supplied Betti data.
-/
theorem conf3_spin_tiled_rank32_of_external_data
    (data : ExternalBettiData)
    (hAmbient : HasConf3AmbientDimension data)
    (hConsistent : RankDataConsistent data)
    (hRank : data.totalRank = 8) :
    data.totalRank * spinTilingMultiplicity = 32 :=
  spin_tiled_rank_from_external_data data hAmbient hConsistent hRank

/--
Combined theorem-safe packet for the current twistor/amplituhedron boundary
lane.
-/
theorem twistor_amplituhedron_boundary_packet
    (S : AmplituhedronBoundarySpec)
    (X₁ X₂ X₃ : Vec22)
    (hTriple : TripleNonNull X₁ X₂ X₃)
    (hBCFW : S.bcfwComparison)
    (hRoh : S.rohozhkinComparison) :
    ((¬ ∃ Z : Twistor, Incident Z X₁ ∧ Incident Z X₂ ∧ Z.2 ≠ 0) ∧
      (¬ ∃ Z : Twistor, Incident Z X₂ ∧ Incident Z X₃ ∧ Z.2 ≠ 0) ∧
      (¬ ∃ Z : Twistor, Incident Z X₃ ∧ Incident Z X₁ ∧ Z.2 ≠ 0)) ∧
      candidateLocalBettiData.totalRank * spinTilingMultiplicity = 32 ∧
      S.bcfwComparison ∧ S.rohozhkinComparison := by
  exact ⟨triple_nonnull_excludes_pairwise_common_twistors X₁ X₂ X₃ hTriple,
    candidate_conf3_spin_tiled_rank32,
    hBCFW,
    hRoh⟩

end InfoGeometry.Projective.TwistorAmplituhedronBoundary
