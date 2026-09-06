import Mathlib

namespace InfoGeometry.Cartan

variable {𝕜 E : Type*} [Field 𝕜] [Invertible (2 : 𝕜)]
variable [AddCommGroup E] [Module 𝕜 E]

/-- A Cartan involution on a module is represented canonically in Mathlib as a LinearEquiv
that is its own inverse. -/
def IsCartanInvolution (θ : E ≃ₗ[𝕜] E) : Prop :=
  (θ : E →ₗ[𝕜] E).comp (θ : E →ₗ[𝕜] E) = LinearMap.id

variable (θ : E ≃ₗ[𝕜] E) (hθ : IsCartanInvolution θ)

/-- Projection to the +1 eigenspace: P₊ = 1/2 (id + θ). -/
noncomputable def Pplus : E →ₗ[𝕜] E :=
  (⅟(2 : 𝕜)) • (LinearMap.id + (θ : E →ₗ[𝕜] E))

/-- Projection to the -1 eigenspace: P₋ = 1/2 (id - θ). -/
noncomputable def Pminus : E →ₗ[𝕜] E :=
  (⅟(2 : 𝕜)) • (LinearMap.id - (θ : E →ₗ[𝕜] E))

/-- The sum of the projectors `Pplus` and `Pminus` is the identity map. -/
lemma Pplus_add_Pminus_eq_id : Pplus θ + Pminus θ = LinearMap.id := by
  dsimp [Pplus, Pminus]
  rw [← smul_add]
  have h_sum : (LinearMap.id + (θ : E →ₗ[𝕜] E)) + (LinearMap.id - (θ : E →ₗ[𝕜] E)) = (2 : 𝕜) • LinearMap.id := by
    ext x; simp; rw [two_smul]
  rw [h_sum, smul_smul, invOf_mul_self, one_smul]

/--
**Cartan Decomposition Lemma**: Any vector `x` is the sum of its eigen-components.
x = P₊ x + P₋ x.
-/
lemma decompose (x : E) : x = Pplus θ x + Pminus θ x := by
  have h_id := LinearMap.congr_fun (Pplus_add_Pminus_eq_id θ) x
  rw [LinearMap.add_apply] at h_id
  exact h_id.symm

/-- θ fixes the + component (the compact/k-space part). -/
@[simp]
lemma theta_Pplus (hθ : IsCartanInvolution θ) (x : E) : θ (Pplus θ x) = Pplus θ x := by
  have h_invol : ∀ y, θ (θ y) = y := fun y => LinearMap.congr_fun hθ y
  show θ ((⅟ 2 : 𝕜) • (x + θ x)) = (⅟ 2 : 𝕜) • (x + θ x)
  rw [map_smul, map_add, h_invol, add_comm]

/-- θ negates the - component (the non-compact/p-space part). -/
@[simp]
lemma theta_Pminus (hθ : IsCartanInvolution θ) (x : E) : θ (Pminus θ x) = - Pminus θ x := by
  have h_invol : ∀ y, θ (θ y) = y := fun y => LinearMap.congr_fun hθ y
  show θ ((⅟ 2 : 𝕜) • (x - θ x)) = -((⅟ 2 : 𝕜) • (x - θ x))
  rw [map_smul, map_sub, h_invol]
  rw [smul_sub, ← neg_sub, smul_sub]

/-- Existence version of the decomposition. -/
theorem eigenspace_involution_decomposition (hθ : IsCartanInvolution θ) (x : E) :
    ∃ (u v : E), x = u + v ∧ θ u = u ∧ θ v = -v :=
  ⟨Pplus θ x, Pminus θ x, decompose θ x, theta_Pplus θ hθ x, theta_Pminus θ hθ x⟩

/-- k-space (compact part) as a submodule. -/
noncomputable def k : Submodule 𝕜 E := LinearMap.range (Pplus θ)

/-- p-space (non-compact part) as a submodule. -/
noncomputable def p : Submodule 𝕜 E := LinearMap.range (Pminus θ)

end InfoGeometry.Cartan
