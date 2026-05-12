import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

open InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

#check @ContinuousLinearEquiv.ofBijective_apply_symm_apply
#check @Submodule.starProjection_eq_self_iff
