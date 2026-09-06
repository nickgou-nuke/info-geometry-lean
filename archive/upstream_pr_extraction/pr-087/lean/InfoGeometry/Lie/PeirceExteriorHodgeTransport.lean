import InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge
import InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge
import InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors

noncomputable section

namespace InfoGeometry.Lie.PeirceExteriorHodgeTransport

open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
open InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge
open InfoGeometry.Lie.SplitOctonionPeirceNativeProjectors
open InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge

theorem hodgeStar_gradedChirality_anticommutes :
    hodgeStar ∘ₗ gradedChirality =
      -(gradedChirality ∘ₗ hodgeStar) := by
  apply LinearMap.ext
  intro x
  ext <;> simp [hodgeStar, gradedChirality, LinearMap.comp_apply]

noncomputable def peirceHodgeStar :
    PeirceCarrier →ₗ[ℝ] PeirceCarrier :=
  (peirceExterior3Equiv.conjAlgEquiv ℝ) hodgeStar

noncomputable def peirceGradedChirality :
    PeirceCarrier →ₗ[ℝ] PeirceCarrier :=
  (peirceExterior3Equiv.conjAlgEquiv ℝ) gradedChirality

theorem peirceHodgeStar_apply
    (x : Exterior3Coordinates) :
    peirceHodgeStar (peirceExterior3Equiv x) =
      peirceExterior3Equiv (hodgeStar x) := by
  rw [peirceHodgeStar, LinearEquiv.conjAlgEquiv_apply]
  change peirceExterior3Equiv
      (hodgeStar (peirceExterior3Equiv.symm (peirceExterior3Equiv x))) =
    peirceExterior3Equiv (hodgeStar x)
  rw [peirceExterior3Equiv.symm_apply_apply]

theorem peirceHodgeStar_apply_all
    (y : PeirceCarrier) :
    peirceHodgeStar y =
      peirceExterior3Equiv
        (hodgeStar (peirceExterior3Equiv.symm y)) := by
  rw [peirceHodgeStar, LinearEquiv.conjAlgEquiv_apply]
  rfl

theorem peirceHodgeStar_sq :
    peirceHodgeStar * peirceHodgeStar = 1 := by
  change (peirceExterior3Equiv.conjAlgEquiv ℝ) hodgeStar *
      (peirceExterior3Equiv.conjAlgEquiv ℝ) hodgeStar = 1
  rw [← map_mul, hodgeStar_sq, map_one]

theorem peirceHodgeStar_gradedChirality_anticommutes :
    peirceHodgeStar * peirceGradedChirality =
      -(peirceGradedChirality * peirceHodgeStar) := by
  change (peirceExterior3Equiv.conjAlgEquiv ℝ) hodgeStar *
      (peirceExterior3Equiv.conjAlgEquiv ℝ) gradedChirality =
    -((peirceExterior3Equiv.conjAlgEquiv ℝ) gradedChirality *
      (peirceExterior3Equiv.conjAlgEquiv ℝ) hodgeStar)
  have hcoord : hodgeStar * gradedChirality =
      -(gradedChirality * hodgeStar) := by
    simpa [Module.End.mul_eq_comp] using
      hodgeStar_gradedChirality_anticommutes
  simpa only [map_mul, map_neg] using congrArg
    (fun T : Module.End ℝ Exterior3Coordinates =>
      (peirceExterior3Equiv.conjAlgEquiv ℝ) T) hcoord

theorem peirceGradedChirality_sq :
    peirceGradedChirality * peirceGradedChirality = 1 := by
  change (peirceExterior3Equiv.conjAlgEquiv ℝ) gradedChirality *
      (peirceExterior3Equiv.conjAlgEquiv ℝ) gradedChirality = 1
  rw [← map_mul, gradedChirality_sq, map_one]

theorem peirceHodgeStar_coordinate (x : PeirceCarrier) :
    peirceHodgeStar x =
      ![x 4, x 5, x 6, x 7, x 0, x 1, x 2, x 3] := by
  let y := peirceExterior3Equiv.symm x
  have hx : x = peirceExterior3Equiv y := by
    exact (peirceExterior3Equiv.apply_symm_apply x).symm
  rw [hx, peirceHodgeStar_apply]
  rcases y with ⟨a, b, c, d⟩
  ext i
  fin_cases i <;> simp [hodgeStar, peirceExterior3Equiv, toPeirce, fromPeirce]

/-- Hodge duality exchanges the degree-zero `(+, +)` character line with the
degree-three `(-, -)` character line. -/
theorem peirceHodgeStar_projectorPP_projectorMM :
    peirceHodgeStar * projectorPP =
      projectorMM * peirceHodgeStar * projectorPP := by
  apply LinearMap.ext
  intro x
  change peirceHodgeStar (projectorPP x) =
    projectorMM (peirceHodgeStar (projectorPP x))
  rw [projectorPP_apply, projectorMM_apply,
    peirceHodgeStar_coordinate]
  simp

/-- Hodge duality maps the degree-one `(+, -)` triplet to the degree-two
`(-, +)` triplet. -/
theorem peirceHodgeStar_projectorPM_projectorMP :
    peirceHodgeStar * projectorPM =
      projectorMP * peirceHodgeStar * projectorPM := by
  apply LinearMap.ext
  intro x
  change peirceHodgeStar (projectorPM x) =
    projectorMP (peirceHodgeStar (projectorPM x))
  rw [projectorPM_apply, projectorMP_apply, peirceHodgeStar_coordinate]
  simp

/-- Reverse degree-two to degree-one Hodge transport. -/
theorem peirceHodgeStar_projectorMP_projectorPM :
    peirceHodgeStar * projectorMP =
      projectorPM * peirceHodgeStar * projectorMP := by
  apply LinearMap.ext
  intro x
  change peirceHodgeStar (projectorMP x) =
    projectorPM (peirceHodgeStar (projectorMP x))
  rw [projectorMP_apply, projectorPM_apply, peirceHodgeStar_coordinate]
  simp

/-- Reverse degree-three to degree-zero Hodge transport. -/
theorem peirceHodgeStar_projectorMM_projectorPP :
    peirceHodgeStar * projectorMM =
      projectorPP * peirceHodgeStar * projectorMM := by
  apply LinearMap.ext
  intro x
  change peirceHodgeStar (projectorMM x) =
    projectorPP (peirceHodgeStar (projectorMM x))
  rw [projectorMM_apply, projectorPP_apply,
    peirceHodgeStar_coordinate]
  simp

end InfoGeometry.Lie.PeirceExteriorHodgeTransport
