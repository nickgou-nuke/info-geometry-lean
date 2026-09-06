import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
import InfoGeometry.Lie.PeirceExteriorHodgeTransport
import InfoGeometry.Exceptional.G2ChiralBivectorCarriers
import InfoGeometry.Algebra.Zorn.G2GaloisCorrespondence

/-!
# Graded projector actions on the circular `1+3+3+1` carrier

This owner connects four repository-native layers without identifying their
multiplication laws:

1. the literal exterior-degree projectors on
   `ExteriorAlgebra ℝ (Fin 3 → ℝ)`;
2. the native Peirce character projectors of ranks `1,3,3,1`;
3. the established Hodge involution exchanging complementary degrees;
4. the four-plane Artin/cyclotomic operator lift.

The Artin lift is block diagonal in the four planes
`{u+,u-}`, `{U_i,V_i}`. Consequently it preserves Hodge-dual *pairs* of
exterior degrees rather than preserving each exterior degree separately.

The finite-`F₂` Galois-connection owner is kept separate: it supplies fixed-set
facts for `0` and `1`, not a cyclotomic field-Galois action on character labels.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonion1331GradedProjectorActionBridge

open scoped BigOperators

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
open InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
open InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors
open InfoGeometry.Lie.PeirceExteriorHodgeTransport
open InfoGeometry.Exceptional.G2ChiralBivectorCarriers
open InfoGeometry.Algebra.Zorn.G2GaloisCorrespondence
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev Exterior3 :=
  InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.Exterior3
abbrev PeirceCarrier := Fin 8 → ℝ

/-! ## 1. Literal exterior projectors equal the native Peirce character projectors -/

/-- Degree `0` transports to the native rank-one `PP` Peirce projector. -/
theorem exteriorDegree0_transport_projectorPP (x : Exterior3) :
    exterior3SplitOctonionCoordinateEquiv (exteriorDegreeProjector1331 0 x) =
      projectorPP (exterior3SplitOctonionCoordinateEquiv x) := by
  change degreeCoordinateProjector 0 (exterior3SplitOctonionCoordinateEquiv x) =
    projectorPP (exterior3SplitOctonionCoordinateEquiv x)
  ext i
  fin_cases i <;>
    simp [degreeCoordinateProjector, exteriorDegree1331, projectorPP_apply]

/-- Degree `1` transports to the native rank-three `PM` Peirce projector. -/
theorem exteriorDegree1_transport_projectorPM (x : Exterior3) :
    exterior3SplitOctonionCoordinateEquiv (exteriorDegreeProjector1331 1 x) =
      projectorPM (exterior3SplitOctonionCoordinateEquiv x) := by
  change degreeCoordinateProjector 1 (exterior3SplitOctonionCoordinateEquiv x) =
    projectorPM (exterior3SplitOctonionCoordinateEquiv x)
  ext i
  fin_cases i <;>
    simp [degreeCoordinateProjector, exteriorDegree1331, projectorPM_apply]

/-- Degree `2` transports to the native rank-three `MP` Peirce projector. -/
theorem exteriorDegree2_transport_projectorMP (x : Exterior3) :
    exterior3SplitOctonionCoordinateEquiv (exteriorDegreeProjector1331 2 x) =
      projectorMP (exterior3SplitOctonionCoordinateEquiv x) := by
  change degreeCoordinateProjector 2 (exterior3SplitOctonionCoordinateEquiv x) =
    projectorMP (exterior3SplitOctonionCoordinateEquiv x)
  ext i
  fin_cases i <;>
    simp [degreeCoordinateProjector, exteriorDegree1331, projectorMP_apply]

/-- Degree `3` transports to the native rank-one `MM` Peirce projector. -/
theorem exteriorDegree3_transport_projectorMM (x : Exterior3) :
    exterior3SplitOctonionCoordinateEquiv (exteriorDegreeProjector1331 3 x) =
      projectorMM (exterior3SplitOctonionCoordinateEquiv x) := by
  change degreeCoordinateProjector 3 (exterior3SplitOctonionCoordinateEquiv x) =
    projectorMM (exterior3SplitOctonionCoordinateEquiv x)
  ext i
  fin_cases i <;>
    simp [degreeCoordinateProjector, exteriorDegree1331, projectorMM_apply]

/-- The native Peirce character projectors reproduce the exact `1+3+3+1`
trace packet. -/
theorem exterior_peirce_projector_trace_packet :
    (LinearMap.trace ℝ PeirceCarrier projectorPP,
      LinearMap.trace ℝ PeirceCarrier projectorPM,
      LinearMap.trace ℝ PeirceCarrier projectorMP,
      LinearMap.trace ℝ PeirceCarrier projectorMM) = (1, 3, 3, 1) :=
  nativeProjectorTrace_packet

/-! ## 2. Hodge duality exchanges complementary projector sectors -/

/-- The canonical Hodge star exchanges the four native projector sectors in
exactly the exterior pattern `0↔3`, `1↔2`. -/
theorem hodge_complementary_projector_packet :
    peirceHodgeStar * projectorPP =
        projectorMM * peirceHodgeStar * projectorPP ∧
    peirceHodgeStar * projectorPM =
        projectorMP * peirceHodgeStar * projectorPM ∧
    peirceHodgeStar * projectorMP =
        projectorPM * peirceHodgeStar * projectorMP ∧
    peirceHodgeStar * projectorMM =
        projectorPP * peirceHodgeStar * projectorMM := by
  exact ⟨peirceHodgeStar_projectorPP_projectorMM,
    peirceHodgeStar_projectorPM_projectorMP,
    peirceHodgeStar_projectorMP_projectorPM,
    peirceHodgeStar_projectorMM_projectorPP⟩

/-- Hodge duality is involutive on the Peirce/exterior coordinate carrier. -/
theorem hodge_involutive_on_1331 :
    peirceHodgeStar * peirceHodgeStar = 1 :=
  peirceHodgeStar_sq

/-- Hodge duality anticommutes with exterior graded chirality. -/
theorem hodge_anticommutes_graded_chirality :
    peirceHodgeStar * peirceGradedChirality =
      -(peirceGradedChirality * peirceHodgeStar) :=
  peirceHodgeStar_gradedChirality_anticommutes

/-! ## 3. Creation/annihilation are arrows between projector sectors -/

/-- The degree-zero Peirce projector fixes the literal exterior vacuum. -/
theorem degreeZero_projector_fixes_vacuum :
    exteriorDegreeProjector1331 0 (1 : Exterior3) = 1 := by
  rw [← peirceVacuum_eq_exteriorVacuum]
  rw [exteriorDegreeProjector1331_basis]
  simp [exteriorDegree1331]

/-- The degree-one projector fixes each one-particle state created from the
vacuum by a native exterior creation operator. -/
theorem degreeOne_projector_fixes_created_vacuum (i : Fin 3) :
    exteriorDegreeProjector1331 1
        (exteriorWedge3 (Pi.single i 1) (1 : Exterior3)) =
      exteriorWedge3 (Pi.single i 1) (1 : Exterior3) := by
  rw [← peirceVacuum_eq_exteriorVacuum, peirceDegreeOne_from_vacuum]
  rw [exteriorDegreeProjector1331_basis]
  fin_cases i <;> simp [exteriorDegree1331]

/-- The dual first-three Clifford channels annihilate the same pure-spinor
vacuum. Together with the preceding theorem this is the native
creation/projector/annihilator generator packet. -/
theorem creation_projector_annihilator_packet (i : Fin 3) :
    exteriorDegreeProjector1331 0 (1 : Exterior3) = 1 ∧
    exteriorDegreeProjector1331 1
        (exteriorWedge3 (Pi.single i 1) (1 : Exterior3)) =
      exteriorWedge3 (Pi.single i 1) (1 : Exterior3) ∧
    (0, dualBasisVector (firstThreeIndex i)) ∈
      neutralAnnihilator (1 : Spinor) := by
  exact ⟨degreeZero_projector_fixes_vacuum,
    degreeOne_projector_fixes_created_vacuum i,
    firstThree_dual_channels_mem_vacuum_annihilator i⟩

/-! ## 4. Artin four-plane lift preserves Hodge-paired planes -/

/-- Reindex the four planes as the established Peirce order:
`(k,0) ↦ k`, `(k,1) ↦ k+4`. -/
def fourPlanePeirceIndex (p : Fin 4 × Fin 2) : Fin 8 :=
  ⟨p.1.1 + 4 * p.2.1, by omega⟩

@[simp] theorem fourPlanePeirceIndex_lower (k : Fin 4) :
    fourPlanePeirceIndex (k, 0) = ⟨k.1, by omega⟩ := by
  apply Fin.ext
  simp [fourPlanePeirceIndex]

@[simp] theorem fourPlanePeirceIndex_upper (k : Fin 4) :
    fourPlanePeirceIndex (k, 1) = ⟨k.1 + 4, by omega⟩ := by
  apply Fin.ext
  simp [fourPlanePeirceIndex]

/-- The two entries in every Artin four-plane carry complementary exterior
degrees. Plane `0` is `0↔3`; the three rail planes are `1↔2`. -/
theorem fourPlane_exteriorDegree_complement (k : Fin 4) :
    exteriorDegree1331 (fourPlanePeirceIndex (k, 0)) +
      exteriorDegree1331 (fourPlanePeirceIndex (k, 1)) = 3 := by
  fin_cases k <;> rfl

/-- A four-plane lift has no matrix coefficient between distinct planes. -/
theorem fourPlaneLift_off_plane_zero
    {R : Type*} [CommRing R]
    (B : Matrix (Fin 2) (Fin 2) R)
    (k l : Fin 4) (c d : Fin 2) (hkl : k ≠ l) :
    fourPlaneLift B (k, c) (l, d) = 0 := by
  simp [fourPlaneLift, hkl]

/-- Multiplying a four-plane lift by a cyclotomic scalar does not change its
plane support. -/
theorem cyclotomic_fourPlaneLift_off_plane_zero
    {R : Type*} [CommRing R]
    (zeta : R) (B : Matrix (Fin 2) (Fin 2) R)
    (k l : Fin 4) (c d : Fin 2) (hkl : k ≠ l) :
    (zeta • fourPlaneLift B) (k, c) (l, d) = 0 := by
  change zeta * fourPlaneLift B (k, c) (l, d) = 0
  rw [fourPlaneLift_off_plane_zero B k l c d hkl]
  simp

/-- Exact Artin/cyclotomic packet on the same four Hodge-paired planes. -/
theorem artin_cyclotomic_hodgePlane_packet
    {R : Type*} [CommRing R]
    (r3 zeta : R) (hr3 : r3 ^ 2 = 3) (hzeta : zeta ^ 6 = -1) :
    (fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3) *
        fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3) *
        fourPlaneLift (BsCartan r3) * fourPlaneLift (BlCartan r3) =
      fourPlaneLift (BlCartan r3) * fourPlaneLift (BsCartan r3) *
        fourPlaneLift (BlCartan r3) * fourPlaneLift (BsCartan r3) *
        fourPlaneLift (BlCartan r3) * fourPlaneLift (BsCartan r3)) ∧
    ((zeta • (fourPlaneLift (BsCartan r3) *
        fourPlaneLift (BlCartan r3))) ^ 6 = -1) ∧
    ((zeta • (fourPlaneLift (BsCartan r3) *
        fourPlaneLift (BlCartan r3))) ^ 12 = 1) := by
  refine ⟨fourPlaneLift_artin_six r3 hr3, ?_⟩
  exact fourPlaneLift_spin_coxeter_twelve r3 zeta hr3 hzeta

/-! ## 5. The native finite Galois connection remains a separate symmetry lane -/

/-- `0` and `1` are fixed by every subgroup in the native finite Galois
connection. This is the exact theorem-level intersection available in the
current `F₂` owner; no cyclotomic field-Galois identification is asserted. -/
theorem finiteGalois_zero_one_fixed (H : Subgroup SplitOctF2Aut) :
    zero ∈ galoisFixedSet H ∧ one ∈ galoisFixedSet H := by
  exact ⟨zero_mem_galoisFixedSet H, one_mem_galoisFixedSet H⟩

/-- Consolidated theorem-level corridor. The exterior projector decomposition
is exactly the Peirce character decomposition; Hodge exchanges complementary
sectors; native creation reaches the degree-one sector from the vacuum; and
Artin/cyclotomic lifts remain inside the four Hodge-paired planes. -/
theorem graded_projector_action_corridor (i : Fin 3) :
    (LinearMap.trace ℝ PeirceCarrier projectorPP,
      LinearMap.trace ℝ PeirceCarrier projectorPM,
      LinearMap.trace ℝ PeirceCarrier projectorMP,
      LinearMap.trace ℝ PeirceCarrier projectorMM) = (1, 3, 3, 1) ∧
    peirceHodgeStar * peirceHodgeStar = 1 ∧
    exteriorDegreeProjector1331 1
        (exteriorWedge3 (Pi.single i 1) (1 : Exterior3)) =
      exteriorWedge3 (Pi.single i 1) (1 : Exterior3) ∧
    (0, dualBasisVector (firstThreeIndex i)) ∈
      neutralAnnihilator (1 : Spinor) := by
  exact ⟨exterior_peirce_projector_trace_packet,
    hodge_involutive_on_1331,
    degreeOne_projector_fixes_created_vacuum i,
    firstThree_dual_channels_mem_vacuum_annihilator i⟩

end InfoGeometry.Canonical.SplitOctonion1331GradedProjectorActionBridge
