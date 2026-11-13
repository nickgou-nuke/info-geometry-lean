/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.KleinPinSmoothMorita
import InfoGeometry.Geometry.KleinPinFrameFamily

/-!
# Compatibility of concrete Klein Pin frames and smooth Morita reduction

The two established constructions use the same actual smooth domains. Their
coordinate square commutes: framing both sectors then reducing with the
transported volume equals reducing first then framing both coefficient
components. The coefficient algebra is the full real endomorphism algebra of
the positive smooth sector, and every matrix entry is transported by its
actual conjugation equivalence.

Consequently the geometric grading, the complete off-diagonal Dirac matrix,
the represented split-Clifford head, and the head-compensated corner all obey
the same frame comparison. The explicit noncommuting circle Pin family gives
jointly smooth evaluated coordinates and reduced differential images.

These are smooth-domain and algebraic operator results. No Hilbert completion,
bounded Fredholm seed, unbounded operator-norm topology, or analytic Hilbert
Morita equivalence is inferred.
-/

noncomputable section

open scoped Matrix ContDiff

namespace InfoGeometry.Geometry.KleinPinMoritaFamily

open InfoGeometry.Geometry.KleinPinDirac
open InfoGeometry.Geometry.KleinPinSmoothMorita
open InfoGeometry.Geometry.KleinPinFrameFamily
open InfoGeometry.Clifford.FreedKleinRepresentation
open InfoGeometry.Topology.KleinCliffordPinLift
open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.OperatorAlgebra.GradedMatrixMorita

/-- Componentwise transport on the actual positive smooth-sector coordinates. -/
def coordinateFrame (U : Spinor ≃ₗ[ℂ] Spinor) :
    (Fin 2 → smoothSections false) ≃ₗ[ℝ] (Fin 2 → framedSmoothSections U false) :=
  LinearEquiv.piCongrRight (fun _ : Fin 2 => frameSmoothEquiv U false)

@[simp] theorem coordinateFrame_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (v : Fin 2 → smoothSections false) (i : Fin 2) :
    coordinateFrame U v i = frameSmoothEquiv U false (v i) := rfl

@[simp] theorem coordinateFrame_symm_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (v : Fin 2 → framedSmoothSections U false) (i : Fin 2) :
    (coordinateFrame U).symm v i = (frameSmoothEquiv U false).symm (v i) := rfl

/-- The concrete sector coordinates on each actual framed smooth domain. -/
def framedSectorCoordinates (U : Spinor ≃ₗ[ℂ] Spinor) :
    FramedTotalSections U ≃ₗ[ℝ] (Fin 2 → framedSmoothSections U false) :=
  (frameTotalEquiv U).symm.trans (sectorCoordinates.trans (coordinateFrame U))

@[simp] theorem framedSectorCoordinates_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (ψ : FramedTotalSections U) (i : Fin 2) :
    framedSectorCoordinates U ψ i =
      frameSmoothEquiv U false (sectorCoordinates ((frameTotalEquiv U).symm ψ) i) := rfl

@[simp] theorem framedSectorCoordinates_symm_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (v : Fin 2 → framedSmoothSections U false) :
    (framedSectorCoordinates U).symm v =
      frameTotalEquiv U (sectorCoordinates.symm ((coordinateFrame U).symm v)) := rfl

/-- The first coordinate is the original positive framed section. -/
@[simp] theorem framedSectorCoordinates_zero (U : Spinor ≃ₗ[ℂ] Spinor)
    (ψ : FramedTotalSections U) : framedSectorCoordinates U ψ 0 = ψ.1 := by
  change frameSmoothEquiv U false ((frameSmoothEquiv U false).symm ψ.1) = ψ.1
  exact (frameSmoothEquiv U false).apply_symm_apply _

/-- The second coordinate uses the conjugated Clifford volume, not the fixed
volume of the unframed fibre representation. -/
theorem framedSectorCoordinates_one_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (ψ : FramedTotalSections U) (p : PlanePoint) :
    (framedSectorCoordinates U ψ 1).val.val p =
      -(framedVolumeAction U (ψ.2.val.val p)) := by
  change U (-volumeAction (U.symm (ψ.2.val.val p))) =
    -(U (volumeAction (U.symm (ψ.2.val.val p))))
  exact U.map_neg _

/-- The full domain comparison square commutes before taking any operator
corner, on both smooth sectors simultaneously. -/
theorem framedSectorCoordinates_frame (U : Spinor ≃ₗ[ℂ] Spinor)
    (ψ : TotalSections) :
    framedSectorCoordinates U (frameTotalEquiv U ψ) =
      coordinateFrame U (sectorCoordinates ψ) := by
  funext i
  rw [framedSectorCoordinates_apply, (frameTotalEquiv U).symm_apply_apply]
  rfl

/-- The coefficient algebra on each actual framed positive smooth domain. -/
abbrev FramedCoeff (U : Spinor ≃ₗ[ℂ] Spinor) :=
  Module.End ℝ (framedSmoothSections U false)

/-- Conjugation transports the entire noncommutative coefficient algebra. -/
def coefficientFrame (U : Spinor ≃ₗ[ℂ] Spinor) : Coeff ≃ₐ[ℝ] FramedCoeff U :=
  (frameSmoothEquiv U false).conjAlgEquiv ℝ

@[simp] theorem coefficientFrame_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (A : Coeff) (ψ : framedSmoothSections U false) :
    coefficientFrame U A ψ =
      frameSmoothEquiv U false (A ((frameSmoothEquiv U false).symm ψ)) := rfl

/-- Actual conjugation on all real linear operators of the doubled smooth domain. -/
def totalOperatorFrame (U : Spinor ≃ₗ[ℂ] Spinor) :
    Module.End ℝ TotalSections ≃ₐ[ℝ] Module.End ℝ (FramedTotalSections U) :=
  (frameTotalEquiv U).conjAlgEquiv ℝ

@[simp] theorem totalOperatorFrame_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (T : Module.End ℝ TotalSections) (ψ : FramedTotalSections U) :
    totalOperatorFrame U T ψ =
      frameTotalEquiv U (T ((frameTotalEquiv U).symm ψ)) := rfl

/-- Matrix coordinates for every operator on the framed smooth domain. -/
def framedOperatorMatrix (U : Spinor ≃ₗ[ℂ] Spinor) :
    Module.End ℝ (FramedTotalSections U) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) (FramedCoeff U) :=
  ((framedSectorCoordinates U).conjAlgEquiv ℝ).trans
    (endVecAlgEquivMatrixEnd (Fin 2) ℝ ℝ (framedSmoothSections U false))

/-- Matrix entries are actual injection/operator/projection composites. -/
theorem framedOperatorMatrix_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (T : Module.End ℝ (FramedTotalSections U))
    (i j : Fin 2) (ψ : framedSmoothSections U false) :
    framedOperatorMatrix U T i j ψ =
      framedSectorCoordinates U
        (T ((framedSectorCoordinates U).symm (Pi.single j ψ))) i := rfl

private theorem coordinateFrame_symm_single (U : Spinor ≃ₗ[ℂ] Spinor)
    (j : Fin 2) (ψ : framedSmoothSections U false) :
    (coordinateFrame U).symm (Pi.single j ψ) =
      Pi.single j ((frameSmoothEquiv U false).symm ψ) := by
  funext i
  by_cases h : i = j
  · subst i
    simp
  · simp [Pi.single_apply, h, Ne.symm h]

/-- Every entry of the full operator-valued matrix obeys the concrete frame
comparison, preserving arbitrary noncommutative coefficient operators. -/
theorem framedOperatorMatrix_natural (U : Spinor ≃ₗ[ℂ] Spinor)
    (T : Module.End ℝ TotalSections) :
    framedOperatorMatrix U (totalOperatorFrame U T) =
      (coefficientFrame U).mapMatrix (operatorMatrix T) := by
  funext i j
  apply LinearMap.ext
  intro ψ
  rw [framedOperatorMatrix_apply, framedSectorCoordinates_symm_apply,
    totalOperatorFrame_apply, (frameTotalEquiv U).symm_apply_apply,
    framedSectorCoordinates_frame, coordinateFrame_apply,
    coordinateFrame_symm_single]
  rfl

@[simp] theorem totalOperatorFrame_grading (U : Spinor ≃ₗ[ℂ] Spinor) :
    totalOperatorFrame U grading = framedGrading U := by
  apply LinearMap.ext
  intro ψ
  rw [totalOperatorFrame_apply, frameTotalEquiv_grading,
    (frameTotalEquiv U).apply_symm_apply]

@[simp] theorem totalOperatorFrame_dirac (U : Spinor ≃ₗ[ℂ] Spinor) :
    totalOperatorFrame U gradedDirac = framedGradedDirac U := by
  apply LinearMap.ext
  intro ψ
  rw [totalOperatorFrame_apply, frameTotalEquiv_dirac,
    (frameTotalEquiv U).apply_symm_apply]

/-- The coefficient carried by the reduction is the actual transported
volume-composed differential operator, with its proved smooth-domain formula. -/
@[simp] theorem coefficientFrame_suspended (U : Spinor ≃ₗ[ℂ] Spinor) :
    coefficientFrame U (suspendedDiracSmoothLinear false) =
      framedSuspendedDiracSmoothLinear U false := rfl

/-- The geometric grading is the same independent head parity in each frame. -/
theorem framedOperatorMatrix_grading (U : Spinor ≃ₗ[ℂ] Spinor) :
    framedOperatorMatrix U (framedGrading U) = !![1, 0; 0, -1] := by
  rw [← totalOperatorFrame_grading, framedOperatorMatrix_natural,
    operatorMatrix_grading]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [AlgEquiv.mapMatrix_apply]

/-- The entire framed differential operator has the transported reduced
operator in both off-diagonal entries, with the same essential minus signs. -/
theorem framedOperatorMatrix_dirac (U : Spinor ≃ₗ[ℂ] Spinor) :
    framedOperatorMatrix U (framedGradedDirac U) =
      !![0, -framedSuspendedDiracSmoothLinear U false;
         -framedSuspendedDiracSmoothLinear U false, 0] := by
  rw [← totalOperatorFrame_dirac, framedOperatorMatrix_natural, operatorMatrix_dirac]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [AlgEquiv.mapMatrix_apply, coefficientFrame_suspended]

/-- Matrix parity agrees with the independently defined framed grading for
every operator, not only for the Dirac coefficients. -/
theorem framedOperatorMatrix_parity (U : Spinor ≃ₗ[ℂ] Spinor)
    (T : Module.End ℝ (FramedTotalSections U)) :
    framedOperatorMatrix U (framedGrading U * T * framedGrading U) =
      matrixGrade (RingEquiv.refl (FramedCoeff U)) (framedOperatorMatrix U T) := by
  rw [map_mul, map_mul, framedOperatorMatrix_grading, matrixGrade_eq_parity_conj]
  change !![1, 0; 0, -1] * framedOperatorMatrix U T * !![1, 0; 0, -1] =
    !![1, 0; 0, -1] * (framedOperatorMatrix U T).map id * !![1, 0; 0, -1]
  rw [Matrix.map_id]

/-- The head compensation is transported by the same actual Pin-frame action. -/
def framedNegativeSwap (U : Spinor ≃ₗ[ℂ] Spinor) :
    Module.End ℝ (FramedTotalSections U) :=
  totalOperatorFrame U negativeSwap

theorem framedNegativeSwap_sq (U : Spinor ≃ₗ[ℂ] Spinor) :
    framedNegativeSwap U * framedNegativeSwap U = 1 := by
  change totalOperatorFrame U negativeSwap * totalOperatorFrame U negativeSwap = 1
  rw [← map_mul, negativeSwap_sq, map_one]

/-- Concrete Morita corner reduction commutes with the frame change. -/
theorem framed_compensated_dirac_corner (U : Spinor ≃ₗ[ℂ] Spinor) :
    framedOperatorMatrix U (framedNegativeSwap U * framedGradedDirac U) 0 0 =
      framedSuspendedDiracSmoothLinear U false := by
  rw [← totalOperatorFrame_dirac]
  change framedOperatorMatrix U
      (totalOperatorFrame U negativeSwap * totalOperatorFrame U gradedDirac) 0 0 = _
  rw [← map_mul, framedOperatorMatrix_natural]
  change coefficientFrame U (operatorMatrix (negativeSwap * gradedDirac) 0 0) = _
  rw [compensated_dirac_corner, coefficientFrame_suspended]

/-- The corner comparison is a typed equality of actual smooth-domain maps. -/
theorem compensated_corner_intertwine (U : Spinor ≃ₗ[ℂ] Spinor) :
    (framedOperatorMatrix U (framedNegativeSwap U * framedGradedDirac U) 0 0).comp
        (frameSmoothEquiv U false).toLinearMap =
      (frameSmoothEquiv U false).toLinearMap.comp
        (operatorMatrix (negativeSwap * gradedDirac) 0 0) := by
  rw [framed_compensated_dirac_corner, compensated_dirac_corner]
  apply LinearMap.ext
  intro ψ
  exact framedSuspendedDiracSmoothLinear_intertwine U false ψ

/-- The same represented split-Clifford head acts on each actual framed domain. -/
def framedCliffordHeadRepresentation (U : Spinor ≃ₗ[ℂ] Spinor) :
    CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11 →ₐ[ℝ]
      Module.End ℝ (FramedTotalSections U) :=
  (totalOperatorFrame U).toAlgHom.comp cliffordHeadRepresentation

theorem framedCliffordHead_volume (U : Spinor ≃ₗ[ℂ] Spinor) :
    framedCliffordHeadRepresentation U InfoGeometry.Clifford.Cl11Matrix.J1_cl =
      framedGrading U := by
  change totalOperatorFrame U
      (cliffordHeadRepresentation InfoGeometry.Clifford.Cl11Matrix.J1_cl) = _
  rw [cliffordHead_volume, totalOperatorFrame_grading]

theorem framedCliffordHead_positive (U : Spinor ≃ₗ[ℂ] Spinor) :
    framedCliffordHeadRepresentation U
      (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0)) =
      -framedNegativeSwap U := by
  change totalOperatorFrame U
      (cliffordHeadRepresentation
        (CliffordAlgebra.ι InfoGeometry.Clifford.Cl11Matrix.q11 (1, 0))) = _
  rw [cliffordHead_positive, map_neg]
  rfl

/-- The full source Clifford grading comparison survives the same frame map. -/
theorem framedCliffordHead_grading (U : Spinor ≃ₗ[ℂ] Spinor)
    (x : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) :
    framedCliffordHeadRepresentation U (CliffordAlgebra.involute x) =
      framedGrading U * framedCliffordHeadRepresentation U x * framedGrading U := by
  change totalOperatorFrame U (cliffordHeadRepresentation (CliffordAlgebra.involute x)) = _
  rw [cliffordHead_grading, map_mul, map_mul, totalOperatorFrame_grading]
  rfl

/-- For the explicit actual Pin family, each evaluated Morita coordinate is
jointly smooth in parameter and covering point. -/
theorem circleCoordinates_joint_contDiff (ψ : TotalSections) (i : Fin 2) :
    ContDiff ℝ ∞ (fun z : ℝ × PlanePoint =>
      (framedSectorCoordinates (circleFrame z.1)
        (frameTotalEquiv (circleFrame z.1) ψ) i).val.val z.2) := by
  simp_rw [framedSectorCoordinates_frame, coordinateFrame_apply]
  exact circleSection_joint_contDiff false (sectorCoordinates ψ i)

/-- Reducing the concrete noncommuting Pin family gives the same jointly
smooth evaluated differential family as transporting its actual corner. -/
theorem circleCorner_joint_contDiff (ψ : smoothSections false) :
    ContDiff ℝ ∞ (fun z : ℝ × PlanePoint =>
      ((framedOperatorMatrix (circleFrame z.1)
          (framedNegativeSwap (circleFrame z.1) * framedGradedDirac (circleFrame z.1))
          0 0) (frameSmoothEquiv (circleFrame z.1) false ψ)).val.val z.2) := by
  simp_rw [framed_compensated_dirac_corner, framedSuspendedDiracSmoothLinear_apply]
  exact circleSuspendedDirac_joint_contDiff false ψ

end InfoGeometry.Geometry.KleinPinMoritaFamily

end
