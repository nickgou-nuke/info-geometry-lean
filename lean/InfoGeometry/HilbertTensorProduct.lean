import Mathlib

open Real
open scoped InnerProductSpace

set_option linter.dupNamespace false

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

lemma hsNorm_sq_eq (A : H₁ →L[ℝ] H₂) : (hsNorm A)^2 = hsInner A A := by sorry

end FiniteDim

end HilbertTensorProduct
