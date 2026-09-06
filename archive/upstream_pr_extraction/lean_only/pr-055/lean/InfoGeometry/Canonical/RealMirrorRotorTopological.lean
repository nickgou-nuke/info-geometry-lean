import Mathlib.Analysis.Normed.Module.FiniteDimension
import InfoGeometry.Canonical.RealMirrorRotorCompatibility
import InfoGeometry.Canonical.RealComplexRotorHomeomorph

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
variable [FiniteDimensional ℝ V]
variable [T2Space V]

noncomputable def realMirrorHomeomorph (J : V ≃ₗ[ℝ] V) : V ≃ₜ V :=
  J.toContinuousLinearEquiv.toHomeomorph

theorem realMirrorHomeomorph_apply (J : V ≃ₗ[ℝ] V) (v : V) :
    realMirrorHomeomorph J v = J v := by
  simp [realMirrorHomeomorph]

theorem mirror_conjugates_realRotorHomeomorph
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I)
    (hI_cont : Continuous I) (J : V ≃ₗ[ℝ] V)
    (hJI : J.toLinearMap.comp I = -I.comp J.toLinearMap)
    (θ : ℝ) :
    (realMirrorHomeomorph J).symm.trans
        ((realRotorHomeomorph I hI hI_cont θ).trans
          (realMirrorHomeomorph J)) =
      realRotorHomeomorph I hI hI_cont (-θ) := by
  ext v
  simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply,
    realMirrorHomeomorph_apply, realRotorHomeomorph_apply]
  change J (realRotorAction I θ (J.symm v)) =
    realRotorAction I (-θ) v
  rw [mirror_realRotorAction_comp I J hJI θ (J.symm v)]
  simp

end

end InfoGeometry.Canonical
