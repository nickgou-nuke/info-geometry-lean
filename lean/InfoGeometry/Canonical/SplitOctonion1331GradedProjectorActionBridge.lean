/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
import InfoGeometry.Lie.PeirceExteriorHodgeTransport
import InfoGeometry.Lie.PeirceExteriorHodgeLinearEquiv
import InfoGeometry.Exceptional.G2ChiralBivectorCarriers
import InfoGeometry.Algebra.Zorn.G2GaloisCorrespondence
import InfoGeometry.Lie.SplitOctonionExteriorParityProjectors
import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.OperatorAlgebra.GradeActionInterface

/-! Transport of the four native degree projectors to the Peirce character
projectors.  The proof is coordinate-free at the carrier boundary: the only
coordinate calculation is the already-owned basis readback. -/

noncomputable section
namespace InfoGeometry.Canonical.SplitOctonion1331GradedProjectorActionBridge

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
open InfoGeometry.Canonical.SplitOctonion1331ExteriorDiracSouriauBridge
open InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors
open InfoGeometry.Lie.SplitOctonionExteriorParityProjectors
open InfoGeometry.Lie.PeirceExteriorHodgeTransport
open InfoGeometry.Exceptional.G2ChiralBivectorCarriers
open InfoGeometry.Algebra.Zorn.G2GaloisCorrespondence
open InfoGeometry.OperatorAlgebra

abbrev Exterior3 := SplitOctonionExterior3HodgeDiracBridge.Exterior3
abbrev PeirceCarrier := InfoGeometry.Algebra.FiniteSpin.Vec8R

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

def peirce1331Projector (k : Fin 4) : Module.End ℝ PeirceCarrier :=
  match k with
  | 0 => projectorPP
  | 1 => projectorPM
  | 2 => projectorMP
  | 3 => projectorMM

def peirce1331Complement (k : Fin 4) : Fin 4 :=
  match k with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0

def peirce1331Grade (k : Fin 4) : Set PeirceCarrier :=
  Set.range (peirce1331Projector k)

theorem peirceHodgeStar_maps_1331_grades :
    MapsToGrade peirce1331Grade
      (fun _ : Unit => peirceHodgeStar)
      (fun _ : Unit => peirce1331Complement) := by
  intro _ k x hx
  rcases hx with ⟨y, rfl⟩
  fin_cases k
  · refine ⟨peirceHodgeStar (projectorPP y), ?_⟩
    simpa [peirce1331Grade, peirce1331Projector, peirce1331Complement,
      Module.End.mul_apply] using
      (congrArg (fun T : Module.End ℝ PeirceCarrier => T y)
        peirceHodgeStar_projectorPP_projectorMM).symm
  · refine ⟨peirceHodgeStar (projectorPM y), ?_⟩
    simpa [peirce1331Grade, peirce1331Projector, peirce1331Complement,
      Module.End.mul_apply] using
      (congrArg (fun T : Module.End ℝ PeirceCarrier => T y)
        peirceHodgeStar_projectorPM_projectorMP).symm
  · refine ⟨peirceHodgeStar (projectorMP y), ?_⟩
    simpa [peirce1331Grade, peirce1331Projector, peirce1331Complement,
      Module.End.mul_apply] using
      (congrArg (fun T : Module.End ℝ PeirceCarrier => T y)
        peirceHodgeStar_projectorMP_projectorPM).symm
  · refine ⟨peirceHodgeStar (projectorMM y), ?_⟩
    simpa [peirce1331Grade, peirce1331Projector, peirce1331Complement,
      Module.End.mul_apply] using
      (congrArg (fun T : Module.End ℝ PeirceCarrier => T y)
        peirceHodgeStar_projectorMM_projectorPP).symm

theorem peirceHodgeStar_image_1331_grade (k : Fin 4) :
    peirceHodgeStarLinearEquiv '' peirce1331Grade k =
      peirce1331Grade (peirce1331Complement k) := by
  apply linearEquiv_mapsToGradeBetween_image_eq
    peirceHodgeStarLinearEquiv peirce1331Grade peirce1331Grade
    peirce1331Complement peirce1331Complement
  · intro i x hx
    rw [peirceHodgeStarLinearEquiv_apply]
    exact peirceHodgeStar_maps_1331_grades () i hx
  · intro i
    have hsymm : ∀ x : PeirceCarrier,
        peirceHodgeStarLinearEquiv.symm x = peirceHodgeStar x := by
      intro x
      apply peirceHodgeStarLinearEquiv.injective
      have hs := congrArg (fun T : Module.End ℝ PeirceCarrier => T x)
        peirceHodgeStar_sq
      simpa [peirceHodgeStarLinearEquiv_apply, Module.End.mul_apply] using hs.symm
    intro x hx
    rw [hsymm]
    exact peirceHodgeStar_maps_1331_grades () i hx
  · intro i
    fin_cases i <;> rfl

noncomputable def peirceHodgeStarEquiv :
    PeirceCarrier ≃ₗ[ℝ] PeirceCarrier :=
  LinearEquiv.ofInvolutive peirceHodgeStar (by
    intro x
    have h := congrArg (fun T : Module.End ℝ PeirceCarrier => T x)
      peirceHodgeStar_sq
    simpa [Module.End.mul_apply] using h)

theorem peirceHodgeStar_maps_1331_grades_image_eq (k : Fin 4) :
    peirceHodgeStarEquiv '' peirce1331Grade k =
      peirce1331Grade (peirce1331Complement k) := by
  apply linearEquiv_mapsToGradeBetween_image_eq peirceHodgeStarEquiv
    peirce1331Grade peirce1331Grade peirce1331Complement peirce1331Complement
  · intro k x hx
    exact peirceHodgeStar_maps_1331_grades () k hx
  · intro k x hx
    exact peirceHodgeStar_maps_1331_grades () k hx
  · intro i
    fin_cases i <;> rfl

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
    {R : Type*} [Ring R]
    (B : Matrix (Fin 2) (Fin 2) R)
    (k l : Fin 4) (c d : Fin 2) (hkl : k ≠ l) :
    fourPlaneLift B (k, c) (l, d) = 0 := by
  simp [fourPlaneLift, hkl]

theorem cyclotomic_fourPlaneLift_off_plane_zero
    {R : Type*} [Ring R]
    (zeta : R) (B : Matrix (Fin 2) (Fin 2) R)
    (k l : Fin 4) (c d : Fin 2) (hkl : k ≠ l) :
    (zeta • fourPlaneLift B) (k, c) (l, d) = 0 := by
  change zeta * fourPlaneLift B (k, c) (l, d) = 0
  rw [fourPlaneLift_off_plane_zero B k l c d hkl]
  simp


theorem exterior_peirce_projector_trace_packet :
    (LinearMap.trace ℝ PeirceCarrier projectorPP,
      LinearMap.trace ℝ PeirceCarrier projectorPM,
      LinearMap.trace ℝ PeirceCarrier projectorMP,
      LinearMap.trace ℝ PeirceCarrier projectorMM) = (1, 3, 3, 1) :=
  nativeProjectorTrace_packet

theorem degreeZero_projector_fixes_vacuum :
    exteriorDegreeProjector1331 0 (1 : Exterior3) = 1 := by
  rw [← peirceVacuum_eq_exteriorVacuum]
  rw [exteriorDegreeProjector1331_basis]
  simp [exteriorDegree1331]

theorem degreeOne_projector_fixes_created_vacuum (i : Fin 3) :
    exteriorDegreeProjector1331 1
        (exteriorWedge3 (Pi.single i 1) (1 : Exterior3)) =
      exteriorWedge3 (Pi.single i 1) (1 : Exterior3) := by
  rw [← peirceVacuum_eq_exteriorVacuum, peirceDegreeOne_from_vacuum]
  rw [exteriorDegreeProjector1331_basis]
  fin_cases i <;> simp [exteriorDegree1331]

theorem finiteGalois_zero_one_fixed
    (H : Subgroup InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.SplitOctF2Aut) :
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.zero ∈ galoisFixedSet H ∧
    InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.one ∈ galoisFixedSet H := by
  exact ⟨InfoGeometry.Algebra.Zorn.G2GaloisCorrespondence.zero_mem_galoisFixedSet H,
    InfoGeometry.Algebra.Zorn.G2GaloisCorrespondence.one_mem_galoisFixedSet H⟩

end InfoGeometry.Canonical.SplitOctonion1331GradedProjectorActionBridge
