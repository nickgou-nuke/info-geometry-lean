import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

open InnerProductSpace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

-- Probe: How to apply codRestrict?
variable (f : E →L[𝕜] F) (p : Submodule 𝕜 F) (h : ∀ x, f x ∈ p)
#check codRestrict f p h
-- Try to find the apply lemma
#check ContinuousLinearMap.codRestrict_apply

-- Probe: Coercion of ContinuousLinearMap to LinearMap
#check (f : E →ₗ[𝕜] F)

-- Probe: ker of ContinuousLinearMap
#check f.ker
#check LinearMap.ker (f : E →ₗ[𝕜] F)

-- Probe: Submodule inf/bot
#check Submodule.inf_orthogonal_eq_bot
