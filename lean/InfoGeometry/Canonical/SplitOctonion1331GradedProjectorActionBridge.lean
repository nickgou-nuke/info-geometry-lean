import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
import InfoGeometry.Lie.PeirceExteriorHodgeTransport
import InfoGeometry.Exceptional.G2ChiralBivectorCarriers
import InfoGeometry.Algebra.Zorn.G2GaloisCorrespondence

/-! Transport of the four native degree projectors to the Peirce character
projectors.  The proof is coordinate-free at the carrier boundary: the only
coordinate calculation is the already-owned basis readback. -/

noncomputable section
namespace InfoGeometry.Canonical.SplitOctonion1331GradedProjectorActionBridge

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
open InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
open InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors
open InfoGeometry.Lie.PeirceExteriorHodgeTransport
open InfoGeometry.Exceptional.G2ChiralBivectorCarriers
open InfoGeometry.Algebra.Zorn.G2GaloisCorrespondence

abbrev Exterior3 := SplitOctonionExterior3HodgeDiracBridge.Exterior3
abbrev PeirceCarrier := Fin 8 → ℝ

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

theorem hodge_involutive_on_1331 :
    peirceHodgeStar * peirceHodgeStar = 1 := peirceHodgeStar_sq

theorem hodge_anticommutes_graded_chirality :
    peirceHodgeStar * peirceGradedChirality =
      -(peirceGradedChirality * peirceHodgeStar) :=
  peirceHodgeStar_gradedChirality_anticommutes

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

theorem fourPlane_exteriorDegree_complement (k : Fin 4) :
    exteriorDegree1331 (fourPlanePeirceIndex (k, 0)) +
      exteriorDegree1331 (fourPlanePeirceIndex (k, 1)) = 3 := by
  fin_cases k <;> rfl

theorem fourPlaneLift_off_plane_zero
    {R : Type*} [CommRing R]
    (B : Matrix (Fin 2) (Fin 2) R)
    (k l : Fin 4) (c d : Fin 2) (hkl : k ≠ l) :
    fourPlaneLift B (k, c) (l, d) = 0 := by
  simp [fourPlaneLift, hkl]

theorem cyclotomic_fourPlaneLift_off_plane_zero
    {R : Type*} [CommRing R]
    (zeta : R) (B : Matrix (Fin 2) (Fin 2) R)
    (k l : Fin 4) (c d : Fin 2) (hkl : k ≠ l) :
    (zeta • fourPlaneLift B) (k, c) (l, d) = 0 := by
  change zeta * fourPlaneLift B (k, c) (l, d) = 0
  rw [fourPlaneLift_off_plane_zero B k l c d hkl]
  simp

end InfoGeometry.Canonical.SplitOctonion1331GradedProjectorActionBridge
