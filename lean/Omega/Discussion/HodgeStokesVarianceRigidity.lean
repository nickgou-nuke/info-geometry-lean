import Mathlib.Tactic

namespace Omega.Discussion

/-- Paper-facing finite-state Hodge--Stokes consequence: an orthogonal decomposition and its
telescoping reduction transfer the variance and endpoint-speed rigidity conclusions. -/
theorem paper_discussion_hodge_stokes_variance_rigidity
    (finiteDimensionalL2EdgeSpace gradientSubspaceClosed coclosedComplementDefined : Prop)
    (orthogonalDecomposition telescopingReduction cltVarianceRigid ldpRateRigid : Prop)
    (hFinite : finiteDimensionalL2EdgeSpace)
    (hGradient : gradientSubspaceClosed)
    (hCoclosed : coclosedComplementDefined)
    (deriveOrthogonalDecomposition :
      finiteDimensionalL2EdgeSpace →
        gradientSubspaceClosed →
          coclosedComplementDefined →
            orthogonalDecomposition)
    (deriveTelescopingReduction : orthogonalDecomposition → telescopingReduction)
    (deriveCltVarianceRigid : telescopingReduction → cltVarianceRigid)
    (deriveLdpRateRigid : telescopingReduction → ldpRateRigid) :
    orthogonalDecomposition ∧
      telescopingReduction ∧
      cltVarianceRigid ∧
      ldpRateRigid := by
  have hOrth : orthogonalDecomposition :=
    deriveOrthogonalDecomposition
      hFinite hGradient hCoclosed
  have hTel : telescopingReduction := deriveTelescopingReduction hOrth
  exact ⟨hOrth, hTel, deriveCltVarianceRigid hTel, deriveLdpRateRigid hTel⟩

end Omega.Discussion
