import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

open InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

#check K.starProjection
#check K.orthogonalProjection
#check K.starProjection_apply
#check K.orthogonalProjection_apply
#check Submodule.starProjection_apply
#check Submodule.orthogonalProjection_apply
#check Submodule.orthogonalProjection_mem_subspace_eq_self
