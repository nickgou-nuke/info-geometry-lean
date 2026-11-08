import InfoGeometry.Canonical.RealComplexRotor
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem mirror_realRotorAction_comp
    (I : V →ₗ[ℝ] V) (J : V ≃ₗ[ℝ] V)
    (hJI : J.toLinearMap.comp I = -I.comp J.toLinearMap)
    (θ : ℝ) (v : V) :
    J (realRotorAction I θ v) =
    realRotorAction I (-θ) (J v) := by
  have hJIv : J (I v) = -(I (J v)) := by
    have h := congrArg (fun f : V →ₗ[ℝ] V => f v) hJI
    change J (I v) = -(I (J v)) at h
    exact h
  unfold realRotorAction
  simp only [map_add, map_smul, Real.cos_neg, Real.sin_neg, hJIv]
  module

end

end InfoGeometry.Canonical
