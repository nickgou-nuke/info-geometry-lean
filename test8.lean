import Mathlib
open scoped InnerProductSpace

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
  [FiniteDimensional ℝ H₁] [FiniteDimensional ℝ H₂]

#check LinearMap.trace
#check ContinuousLinearMap.adjoint_inner_left
