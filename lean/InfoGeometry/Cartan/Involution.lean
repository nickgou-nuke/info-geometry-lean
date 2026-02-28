import Mathlib.Algebra.Module.LinearMap

namespace InfoGeometry.Cartan

variable {𝕜 E : Type*} [LinearOrderedField 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

/-- A Cartan involution on a module: θ² = id. -/
structure CartanInvolution where
  θ : E →ₗ[𝕜] E
  invol : θ.comp θ = LinearMap.id

namespace CartanInvolution

variable (C : CartanInvolution (𝕜 := 𝕜) (E := E))

/-- Projection to the +1 eigenspace: P₊ = 1/2 (id + θ). -/
noncomputable def Pplus : E →ₗ[𝕜] E := ( (1/2 : 𝕜) ) • (LinearMap.id + C.θ)

/-- Projection to the -1 eigenspace: P₋ = 1/2 (id - θ). -/
noncomputable def Pminus : E →ₗ[𝕜] E := ( (1/2 : 𝕜) ) • (LinearMap.id - C.θ)

/-- Decomposition: x = P₊ x + P₋ x. -/
lemma decompose (x : E) : x = (C.Pplus x) + (C.Pminus x) := by
  simp [CartanInvolution.Pplus, CartanInvolution.Pminus, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, smul_add]

/-- θ fixes the + component. -/
lemma theta_Pplus (x : E) : C.θ (C.Pplus x) = C.Pplus x := by
  simp [CartanInvolution.Pplus, LinearMap.map_add, LinearMap.map_smul, C.invol]

/-- θ negates the - component. -/
lemma theta_Pminus (x : E) : C.θ (C.Pminus x) = - C.Pminus x := by
  simp [CartanInvolution.Pminus, sub_eq_add_neg, LinearMap.map_add, LinearMap.map_smul, C.invol]

/-- k-space and p-space as submodules (ranges of the projections). -/
noncomputable def k : Submodule 𝕜 E := LinearMap.range C.Pplus
noncomputable def p : Submodule 𝕜 E := LinearMap.range C.Pminus

end CartanInvolution
end InfoGeometry.Cartan
