import Mathlib

/-!
# Cartan Decomposition

This file implements the Cartan Decomposition Lemma.

The lemma states that for a vector space `E` over a field `k` where `2` is invertible,
a Cartan involution `θ` (a linear map satisfying `θ^2 = I`) induces a unique
decomposition of any vector `x ∈ E` into `+1` and `-1` eigenvectors.

The decomposition is given by `x = P₊ x + P₋ x`, where the projectors are
defined as `P_± = (1/2) * (I ± θ)`.
-/

namespace InfoGeometry.Cartan

variable {𝕜 E : Type*} [Field 𝕜] [Invertible (2 : 𝕜)]
variable [AddCommGroup E] [Module 𝕜 E]

/-- A Cartan involution on a module: θ² = id. -/
structure CartanInvolution (E : Type*) [AddCommGroup E] [Module 𝕜 E] where
  θ : E →ₗ[𝕜] E
  invol : θ.comp θ = LinearMap.id

namespace CartanInvolution

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable (C : CartanInvolution E)

/-- Projection to the +1 eigenspace: P₊ = 1/2 (id + θ). -/
noncomputable def Pplus : E →ₗ[𝕜] E :=
  (⅟(2 : 𝕜)) • (LinearMap.id + C.θ)

/-- Projection to the -1 eigenspace: P₋ = 1/2 (id - θ). -/
noncomputable def Pminus : E →ₗ[𝕜] E :=
  (⅟(2 : 𝕜)) • (LinearMap.id - C.θ)

/-- The sum of the projectors `Pplus` and `Pminus` is the identity map. -/
lemma Pplus_add_Pminus_eq_id : C.Pplus + C.Pminus = LinearMap.id := by
  dsimp [Pplus, Pminus]
  rw [← smul_add]
  have h_sum : (LinearMap.id + C.θ) + (LinearMap.id - C.θ) = (2 : 𝕜) • LinearMap.id := by
    ext x; simp; abel; rw [two_smul]
  rw [h_sum, smul_smul, invOf_mul_self, one_smul]

/--
**Cartan Decomposition Lemma**: Any vector `x` is the sum of its eigen-components.
x = P₊ x + P₋ x.
-/
lemma decompose (x : E) : x = C.Pplus x + C.Pminus x := by
  have h_id := LinearMap.congr_fun C.Pplus_add_Pminus_eq_id x
  rw [LinearMap.add_apply] at h_id
  exact h_id.symm

/-- θ fixes the + component (the compact/k-space part). -/
@[simp]
lemma theta_Pplus (x : E) : C.θ (C.Pplus x) = C.Pplus x := by
  have h_invol : ∀ y, C.θ (C.θ y) = y := fun y => LinearMap.congr_fun C.invol y
  have h_plus_eval : C.Pplus x = (⅟2 : 𝕜) • (x + C.θ x) := rfl
  rw [h_plus_eval, LinearMap.map_smul, LinearMap.map_add, h_invol, add_comm]
  rfl

/-- θ negates the - component (the non-compact/p-space part). -/
@[simp]
lemma theta_Pminus (x : E) : C.θ (C.Pminus x) = - C.Pminus x := by
  have h_invol : ∀ y, C.θ (C.θ y) = y := fun y => LinearMap.congr_fun C.invol y
  have h_minus_eval : C.Pminus x = (⅟2 : 𝕜) • (x - C.θ x) := rfl
  rw [h_minus_eval, LinearMap.map_smul, LinearMap.map_sub, h_invol]
  rw [LinearMap.smul_apply, smul_sub, ← neg_sub, smul_sub]
  rfl

/-- Existence version of the decomposition. -/
theorem eigenspace_involution_decomposition (x : E) :
    ∃ (u v : E), x = u + v ∧ C.θ u = u ∧ C.θ v = -v :=
  ⟨C.Pplus x, C.Pminus x, C.decompose x, C.theta_Pplus x, C.theta_Pminus x⟩

/-- k-space (compact part) as a submodule. -/
noncomputable def k : Submodule 𝕜 E := LinearMap.range C.Pplus

/-- p-space (non-compact part) as a submodule. -/
noncomputable def p : Submodule 𝕜 E := LinearMap.range C.Pminus

end CartanInvolution
end InfoGeometry.Cartan
