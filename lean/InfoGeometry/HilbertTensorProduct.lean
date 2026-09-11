import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Trace

open Real
open scoped InnerProductSpace

namespace HilbertTensorProduct

section FiniteDim

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
  [FiniteDimensional ℝ H₁] [FiniteDimensional ℝ H₂]

noncomputable def hsInner (A B : H₁ →L[ℝ] H₂) : ℝ :=
  LinearMap.trace ℝ H₁ (ContinuousLinearMap.comp (ContinuousLinearMap.adjoint A) B)

omit [FiniteDimensional ℝ H₁] [FiniteDimensional ℝ H₂] in
lemma hsInner_eq_trace_transpose_mul (A B : H₁ →L[ℝ] H₂) :
    hsInner A B = LinearMap.trace ℝ H₁ (ContinuousLinearMap.comp (ContinuousLinearMap.adjoint A) B) :=
  rfl

noncomputable def hsNorm (A : H₁ →L[ℝ] H₂) : ℝ := Real.sqrt (hsInner A A)

omit [FiniteDimensional ℝ H₂] in
lemma hsNorm_sq_eq (A : H₁ →L[ℝ] H₂) : (hsNorm A)^2 = hsInner A A := by
  have h_nonneg : 0 ≤ hsInner A A := by
    let b := stdOrthonormalBasis ℝ H₁
    rw [hsInner, LinearMap.trace_eq_sum_inner (ContinuousLinearMap.comp (ContinuousLinearMap.adjoint A) A) b]
    refine Finset.sum_nonneg ?_
    intro i _
    have h_term : 0 ≤ ⟪b i, (ContinuousLinearMap.adjoint A) (A (b i))⟫_ℝ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
      simp
    simpa [ContinuousLinearMap.comp_apply] using h_term
  dsimp [hsNorm]
  nlinarith [sq_sqrt h_nonneg]
end FiniteDim

end HilbertTensorProduct
