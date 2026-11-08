import Mathlib.Analysis.Calculus.FDeriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Module.Dual

noncomputable section

namespace InfoGeometry.Geometry.LegendreDifferential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev ContinuousCovector (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] := E →L[ℝ] ℝ

def legendrePairing (η : ContinuousCovector E) (x : E) : ℝ :=
  topDualPairing ℝ E η x

@[simp] theorem legendrePairing_apply (η : ContinuousCovector E) (x : E) :
    legendrePairing η x = η x := by
  rfl

theorem legendrePairing_eq_evaluation (η : ContinuousCovector E) (x : E) :
    legendrePairing η x = η x := rfl

theorem legendrePairing_eq_topDualPairing
    (η : ContinuousCovector E) (x : E) :
    legendrePairing η x = topDualPairing ℝ E η x :=
  rfl

noncomputable def legendreMap (ψ : E → ℝ) : E → ContinuousCovector E :=
  fun x => fderiv ℝ ψ x

@[simp] theorem legendreMap_apply (ψ : E → ℝ) (x : E) :
    legendreMap ψ x = fderiv ℝ ψ x := rfl

theorem legendreMap_eq_of_hasFDerivAt {ψ : E → ℝ} {x : E}
    {dψ : E →L[ℝ] ℝ} (hψ : HasFDerivAt ψ dψ x) :
    legendreMap ψ x = dψ := hψ.fderiv

noncomputable def hessianMap (ψ : E → ℝ) (x : E) :
    E →L[ℝ] ContinuousCovector E := fderiv ℝ (legendreMap ψ) x

@[simp] theorem hessianMap_apply_def (ψ : E → ℝ) (x u : E) :
    hessianMap ψ x u = fderiv ℝ (legendreMap ψ) x u := rfl

theorem hessianMap_eq_of_hasFDerivAt_legendreMap {ψ : E → ℝ} {x : E}
    {H : E →L[ℝ] ContinuousCovector E}
    (hH : HasFDerivAt (legendreMap ψ) H x) :
    hessianMap ψ x = H := hH.fderiv

theorem hessianMap_apply_eq_of_hasFDerivAt_legendreMap {ψ : E → ℝ} {x : E}
    {H : E →L[ℝ] ContinuousCovector E}
    (hH : HasFDerivAt (legendreMap ψ) H x) (u : E) :
    hessianMap ψ x u = H u := by
  rw [hessianMap_eq_of_hasFDerivAt_legendreMap hH]

noncomputable def algebraicLegendreMap (ψ : E → ℝ) : E → Module.Dual ℝ E :=
  fun x => (legendreMap ψ x).toLinearMap

@[simp] theorem algebraicLegendreMap_apply (ψ : E → ℝ) (x u : E) :
    algebraicLegendreMap ψ x u = fderiv ℝ ψ x u := rfl

theorem algebraicLegendreMap_pairing (ψ : E → ℝ) (x u : E) :
    algebraicLegendreMap ψ x u = legendrePairing (legendreMap ψ x) u := by
  simp [legendrePairing]

end InfoGeometry.Geometry.LegendreDifferential
