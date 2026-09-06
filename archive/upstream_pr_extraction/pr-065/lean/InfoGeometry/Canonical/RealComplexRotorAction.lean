import InfoGeometry.Canonical.RealComplexRotorHomeomorph

namespace InfoGeometry.Canonical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

theorem realRotorHomeomorph_zero
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I)
    (hI_cont : Continuous I) :
    realRotorHomeomorph I hI hI_cont 0 = Homeomorph.refl V := by
  ext v
  simp [realRotorHomeomorph, realRotorAction]

theorem realRotorHomeomorph_trans
    (I : V →ₗ[ℝ] V) (hI : IsRealComplexStructure I)
    (hI_cont : Continuous I) (θ φ : ℝ) :
    (realRotorHomeomorph I hI hI_cont θ).trans
        (realRotorHomeomorph I hI hI_cont φ) =
      realRotorHomeomorph I hI hI_cont (θ + φ) := by
  ext v
  change realRotorAction I φ (realRotorAction I θ v) =
    realRotorAction I (θ + φ) v
  rw [realRotorAction_add I hI, add_comm]

end

end InfoGeometry.Canonical
