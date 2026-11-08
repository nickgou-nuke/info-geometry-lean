import InfoGeometry.Quantum.GeometricTensorSplitOctonionChiralFrame
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Relative and mixed readouts for two chiral frames

This owner separates the relative frame operator from the mixed metric/QGT
operator.  It deliberately does not introduce a logarithm or a determinant:
those require additional positivity and finite-dimensional hypotheses.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Quantum.ChiralVacuumRelativeSurprisalBridge

open InfoGeometry.Quantum.GeometricQuantumTensor
open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

def relativeFrame (Fminus Fplus : H₂ ≃L[ℝ] H₂) : H₂ ≃L[ℝ] H₂ :=
  Fplus.trans Fminus.symm

omit [CompleteSpace E] in
@[simp] theorem relativeFrame_apply
    (Fminus Fplus : H₂ ≃L[ℝ] H₂) (u : H₂) :
    relativeFrame Fminus Fplus u = Fminus.symm (Fplus u) := by
  simp [relativeFrame, ContinuousLinearEquiv.trans_apply]

omit [CompleteSpace E] in
theorem relativeFrame_reverse
    (Fminus Fplus : H₂ ≃L[ℝ] H₂) :
    relativeFrame Fplus Fminus = (relativeFrame Fminus Fplus).symm := by
  rfl

noncomputable def mixedQGTFrameOperator
    (Fplus Fminus : H₂ ≃L[ℝ] H₂) (G₀ : EndH) : EndH :=
  polarizedPullbackMetric Fplus.toContinuousLinearMap
    Fminus.toContinuousLinearMap G₀

theorem mixedQGTFrameOperator_apply
    (Fplus Fminus : H₂ ≃L[ℝ] H₂) (G₀ : EndH) (u v : H₂) :
    metricOfOperator (mixedQGTFrameOperator Fplus Fminus G₀) u v =
      ⟪G₀ (Fplus u), Fminus v⟫_ℝ := by
  exact metricOfOperator_polarizedPullbackMetric_apply
    Fplus.toContinuousLinearMap Fminus.toContinuousLinearMap G₀ u v

theorem mixedQGTFrameOperator_swap
    (Fplus Fminus : H₂ ≃L[ℝ] H₂) (G₀ : EndH)
    (hG : ContinuousLinearMap.adjoint G₀ = G₀) (u v : H₂) :
    metricOfOperator (mixedQGTFrameOperator Fplus Fminus G₀) u v =
      metricOfOperator
        (mixedQGTFrameOperator Fminus Fplus G₀) v u := by
  rw [mixedQGTFrameOperator_apply, mixedQGTFrameOperator_apply]
  rw [real_inner_comm]
  rw [← ContinuousLinearMap.adjoint_inner_right, hG]

theorem mixedQGTFrameOperator_eq_id_of_adjoint_eq_symm
    (Fplus Fminus : H₂ ≃L[ℝ] H₂)
    (hAdj : ContinuousLinearMap.adjoint Fminus.toContinuousLinearMap =
      Fplus.symm.toContinuousLinearMap) :
      mixedQGTFrameOperator Fplus Fminus
        (ContinuousLinearMap.id ℝ H₂) =
      ContinuousLinearMap.id ℝ H₂ := by
  apply ContinuousLinearMap.ext
  intro u
  change ContinuousLinearMap.adjoint Fminus.toContinuousLinearMap
      (Fplus u) = u
  rw [hAdj]
  simp

theorem mixedQGTFrameOperator_eq_of_adjoint_eq_symm_of_commute
    (Fplus Fminus : H₂ ≃L[ℝ] H₂) (G₀ : EndH)
    (hAdj : ContinuousLinearMap.adjoint Fminus.toContinuousLinearMap =
      Fplus.symm.toContinuousLinearMap)
    (hComm : G₀.comp Fplus.toContinuousLinearMap =
      Fplus.toContinuousLinearMap.comp G₀) :
    mixedQGTFrameOperator Fplus Fminus G₀ = G₀ := by
  apply ContinuousLinearMap.ext
  intro u
  change ContinuousLinearMap.adjoint Fminus.toContinuousLinearMap
      (G₀ (Fplus u)) = G₀ u
  have hComm_u : G₀ (Fplus u) = Fplus (G₀ u) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun T : EndH => T u) hComm
  rw [hAdj, hComm_u]
  simp

section Determinant

variable [Module.Free ℝ (DoubledSpace E)] [Module.Finite ℝ (DoubledSpace E)]

noncomputable def relativeFrameDet
    (Fminus Fplus : H₂ ≃L[ℝ] H₂) : ℝˣ :=
  LinearEquiv.det (relativeFrame Fminus Fplus).toLinearEquiv

omit [CompleteSpace E] [Module.Free ℝ H₂] [Module.Finite ℝ H₂] in
theorem relativeFrameDet_transformation
    (Fminus Fplus : H₂ ≃L[ℝ] H₂) :
    relativeFrameDet Fminus Fplus =
      (LinearEquiv.det Fminus.toLinearEquiv)⁻¹ *
        LinearEquiv.det Fplus.toLinearEquiv := by
  simp [relativeFrame, relativeFrameDet, LinearEquiv.det_trans]

omit [CompleteSpace E] [Module.Free ℝ H₂] [Module.Finite ℝ H₂] in
theorem relativeFrameDet_eq_one_of_same_det
    (Fminus Fplus : H₂ ≃L[ℝ] H₂)
    (hdet : LinearEquiv.det Fminus.toLinearEquiv =
      LinearEquiv.det Fplus.toLinearEquiv) :
    relativeFrameDet Fminus Fplus = 1 := by
  rw [relativeFrameDet_transformation, hdet]
  simp

omit [CompleteSpace E] [Module.Free ℝ H₂] [Module.Finite ℝ H₂] in
theorem relativeFrameDet_reverse
    (Fminus Fplus : H₂ ≃L[ℝ] H₂) :
    relativeFrameDet Fplus Fminus = (relativeFrameDet Fminus Fplus)⁻¹ := by
  rw [relativeFrameDet_transformation, relativeFrameDet_transformation]
  simp [mul_comm]

end Determinant

end InfoGeometry.Quantum.ChiralVacuumRelativeSurprisalBridge
