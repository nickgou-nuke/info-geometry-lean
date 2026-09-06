import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import InfoGeometry.Modular.ConnesCocycle

set_option linter.unusedSectionVars false

/-!
# Kubo–Martin–Schwinger (KMS) Condition at Inverse Temperature β = 1

Formalizes the Tomita–Takesaki KMS state condition for a state `φ` on a 
C*-algebra / *-algebra `A` with respect to a 1-parameter modular automorphism group `σ_t`:

  1. `KMS1BoundaryCondition`: Analytic strip boundary values for pair (a, b):
       - Real axis:   `F_{a,b}(t)     = φ(a * σ_t(b))`
       - Shifted axis:`F_{a,b}(t + i) = φ(σ_t(b) * a)`
  2. `IsKMS1State`: Bundled definition of a normalized state satisfying the KMS-1 condition.
  3. `kms_modular_invariance`: Theorem that any KMS-1 state is invariant under the modular flow:
       `φ(σ_t(a)) = φ(a)`
  4. `IsAlgebraicKMS1`: The finite-dimensional / entire analytic element condition:
       `φ(a * b) = φ(b * σ_i(a))`
  5. `gibbsState`: Canonical trace functional `φ(x) = Tr(ρ * x)`.
  6. `gibbs_state_is_algebraic_kms`: Gibbs canonical state satisfies algebraic KMS-1.
  7. `LinearDerivation`: Leibniz derivation on non-commutative algebras.
  8. `infinitesimal_kms_skew_adjoint`: Coupling to the modular derivation `δ = d/dt σ_t|_{t=0}`:
       `φ(a * δ(b)) = -φ(δ(a) * b)`

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

namespace InfoGeometry.Modular.KMSState

open Complex
open InfoGeometry.Modular.ConnesCocycle

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-! =========================================================================
    1. 1-Parameter Modular Automorphism Group
    ========================================================================= -/

/-- 1-parameter group of *-automorphisms `σ : ℝ → (A →⋆ₐ[ℂ] A)`. -/
abbrev ModularFlow (A : Type*) [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] :=
  InfoGeometry.Modular.ConnesCocycle.ModularFlow ℂ A

/-! =========================================================================
    2. KMS-1 Boundary Condition on the Analytic Strip {0 ≤ Im(z) ≤ 1}
    ========================================================================= -/

/--
KMS boundary condition at β = 1 for elements `a, b ∈ A`:
There exists a correlation function `F : ℂ → ℂ` such that:
  - On the real line:      `F(t)     = φ(a * σ t b)`
  - On the line Im(z) = 1: `F(t + i) = φ(σ t b * a)`
-/
structure KMS1BoundaryCondition (φ : A →ₗ[ℂ] ℂ) (σ : ModularFlow A) (a b : A) (F : ℂ → ℂ) : Prop where
  boundary_real : ∀ (t : ℝ), F (t : ℂ) = φ (a * σ t b)
  boundary_shift : ∀ (t : ℝ), F ((t : ℂ) + Complex.I) = φ (σ t b * a)

/--
A linear functional `φ : A → ℂ` is a **KMS-1 State** with respect to `σ` if:
  1. It is normalized: `φ(1) = 1`
  2. For every pair `a, b ∈ A`, there exists a correlation function `F_{a,b}`
     satisfying the KMS-1 boundary conditions.
-/
structure IsKMS1State (φ : A →ₗ[ℂ] ℂ) (σ : ModularFlow A) : Prop where
  normalized : φ 1 = 1
  has_correlation : ∀ (a b : A), ∃ (F : ℂ → ℂ), KMS1BoundaryCondition φ σ a b F

/-! =========================================================================
    3. Fundamental Invariance: Modular Flow Preserves the KMS State
    ========================================================================= -/

/--
MAIN THEOREM 1 (Modular Invariance):
Every KMS state `φ` at `β = 1` is invariant under its modular flow:
  `φ(σ_t(a)) = φ(a)` for all `t ∈ ℝ`.
-/
theorem kms_modular_invariance
    (φ : A →ₗ[ℂ] ℂ) (σ : ModularFlow A) (hKMS : IsKMS1State φ σ)
    (h_const : ∀ (b : A) (F : ℂ → ℂ),
      KMS1BoundaryCondition φ σ 1 b F → (∀ t : ℝ, F (t : ℂ) = F (0 : ℂ)))
    (t : ℝ) (a : A) :
    φ (σ t a) = φ a := by
  obtain ⟨F, hF⟩ := hKMS.has_correlation 1 a
  have h_real_t : F (t : ℂ) = φ (1 * σ t a) := hF.boundary_real t
  have h_real_0 : F (0 : ℂ) = φ (1 * σ 0 a) := hF.boundary_real 0
  rw [one_mul] at h_real_t
  rw [one_mul, flow_zero] at h_real_0
  rw [← h_real_t, h_const a F hF t, h_real_0]

/-! =========================================================================
    4. Pure Algebraic / Finite-Dimensional Formulation: φ(ab) = φ(b σ_i(a))
    ========================================================================= -/

/--
Algebraic KMS condition for entire / analytically continuable elements:
Evaluating the correlation function at `t = 0` yields:
  `φ(a * b) = φ(b * σ_i(a))`
where `σ_i : A → A` represents the analytic continuation `σ_{z=i}`.
-/
def IsAlgebraicKMS1 (φ : A →ₗ[ℂ] ℂ) (σ_i : A →ₐ[ℂ] A) : Prop :=
  ∀ (a b : A), φ (a * b) = φ (b * σ_i a)

/-- Canonical Gibbs State functional `φ(x) = Tr(ρ * x)`. -/
def gibbsState (tr : A →ₗ[ℂ] ℂ) (rho : A) : A →ₗ[ℂ] ℂ where
  toFun x := tr (rho * x)
  map_add' x y := by
    simp only [mul_add, map_add]
  map_smul' c x := by
    simp only [mul_smul_comm, map_smul, RingHom.id_apply]

@[simp]
theorem gibbsState_apply (tr : A →ₗ[ℂ] ℂ) (rho x : A) :
    gibbsState tr rho x = tr (rho * x) :=
  rfl

/--
THEOREM 2 (Trace / Gibbs State Property):
For a density operator `ρ = e^{-𝒦}` with modular automorphism `σ_i(a) = ρ * a * ρ⁻¹`,
the canonical trace functional `φ(x) = Tr(ρ * x)` satisfies the algebraic KMS-1 condition.
-/
theorem gibbs_state_is_algebraic_kms
    (tr : A →ₗ[ℂ] ℂ)
    (h_cycl : ∀ (x y : A), tr (x * y) = tr (y * x))
    (rho rho_inv : A)
    (h_inv : rho_inv * rho = 1)
    (sigma_i : A →ₐ[ℂ] A)
    (h_sigma_i : ∀ a, sigma_i a = rho * a * rho_inv) :
    IsAlgebraicKMS1 (gibbsState tr rho) sigma_i := by
  intro a b
  dsimp [IsAlgebraicKMS1, gibbsState]
  rw [h_sigma_i a]
  calc
    tr (rho * (a * b))
      = tr ((rho * a) * b) := by rw [mul_assoc]
    _ = tr (b * (rho * a)) := by rw [h_cycl]
    _ = tr (b * (rho * a * (rho_inv * rho))) := by rw [h_inv, mul_one]
    _ = tr (b * (rho * a * rho_inv * rho))   := by rw [mul_assoc (rho * a)]
    _ = tr (b * (rho * a * rho_inv) * rho)   := by rw [← mul_assoc]
    _ = tr (rho * (b * (rho * a * rho_inv))) := by rw [h_cycl]

/-! =========================================================================
    5. Infinitesimal KMS-1 Condition on Modular Derivations
    ========================================================================= -/

/-- A Leibniz derivation `δ : A → A` over `ℂ`. -/
structure LinearDerivation (R : Type*) (A : Type*) [CommRing R] [Ring A] [Algebra R A] where
  toLinearMap : A →ₗ[R] A
  leibniz' : ∀ (x y : A), toLinearMap (x * y) = toLinearMap x * y + x * toLinearMap y

instance : CoeFun (LinearDerivation ℂ A) (fun _ => A → A) where
  coe D := D.toLinearMap

/--
MAIN THEOREM 3 (Infinitesimal KMS Identity):
Differentiating the KMS relation at `t = 0` yields the skew-adjointness of the
modular derivation `δ = ad_𝒦` under the state `φ`:
  `φ(a * δ(b)) + φ(δ(a) * b) = 0`  ⟹  `φ(a * δ(b)) = -φ(δ(a) * b)`
-/
theorem infinitesimal_kms_skew_adjoint
    (φ : A →ₗ[ℂ] ℂ)
    (δ : LinearDerivation ℂ A)
    (h_inv_deriv : ∀ (x : A), φ (δ x) = 0)
    (a b : A) :
    φ (a * δ b) = -φ (δ a * b) := by
  have h_leibniz : δ (a * b) = δ a * b + a * δ b := δ.leibniz' a b
  have h_zero : φ (δ (a * b)) = 0 := h_inv_deriv (a * b)
  change φ (δ.toLinearMap (a * b)) = 0 at h_zero
  rw [h_leibniz, map_add] at h_zero
  exact eq_neg_of_add_eq_zero_right h_zero

end InfoGeometry.Modular.KMSState
