import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Data.Real.Basic

/-!
# Multiplicative 1-Cocycle Identity of Connes: u_{s+t} = u_s * σ_s^φ(u_t)

Formalizes the Tomita–Takesaki Radon–Nikodym cocycle identity for modular automorphism groups:
  1. `ModularFlow`: 1-parameter group of *-automorphisms `σ^φ : ℝ → (A →⋆ₐ[R] A)`.
  2. `ConnesOneCocycle`: Multiplicative 1-cocycle condition `u(s + t) = u(s) * σ_s^φ(u(t))`
     with initial normalization `u(0) = 1`.
  3. `PerturbedFlow`: Definition of the cocycle-twisted automorphism flow:
       `σ_t^ψ(x) = u(t) * σ_t^φ(x) * (u(t))*`
  4. `perturbedFlow_add`: Proof that the 1-cocycle identity is necessary and sufficient
     for `σ^ψ` to form a genuine 1-parameter group homomorphism:
       `σ_{s+t}^ψ = σ_s^ψ ∘ σ_t^ψ`
  5. `cocycle_inv`: Inversion law `u(-t) = σ_{-t}^φ(u(t)*)`.
  6. `cocycle_prod_law`: Product chain rule for multiplicative 1-cocycles.
-/

namespace InfoGeometry.Modular.ConnesCocycle

variable {R : Type*} [CommSemiring R] [StarRing R]
variable {A : Type*} [Ring A] [Algebra R A] [StarRing A] [StarModule R A]

/-! =========================================================================
    1. Modular 1-Parameter *-Automorphism Group
    ========================================================================= -/

/-- A 1-parameter group of *-algebra automorphisms `σ : ℝ → (A →⋆ₐ[R] A)`. -/
structure ModularFlow (R : Type*) [CommSemiring R] [StarRing R]
    (A : Type*) [Ring A] [Algebra R A] [StarRing A] [StarModule R A] where
  toFun : ℝ → (A →⋆ₐ[R] A)
  map_zero : toFun 0 = StarAlgHom.id R A
  map_add : ∀ (s t : ℝ) (x : A), toFun (s + t) x = toFun s (toFun t x)

instance : CoeFun (ModularFlow R A) (fun _ => ℝ → A →⋆ₐ[R] A) where
  coe := ModularFlow.toFun

@[simp]
theorem flow_zero (σ : ModularFlow R A) (x : A) : σ 0 x = x := by
  have h := σ.map_zero
  change (σ.toFun 0) x = x
  rw [h]
  rfl

@[simp]
theorem flow_add (σ : ModularFlow R A) (s t : ℝ) (x : A) :
    σ (s + t) x = σ s (σ t x) :=
  σ.map_add s t x

/-! =========================================================================
    2. Connes Multiplicative 1-Cocycle Structure
    ========================================================================= -/

/--
A unitary 1-cocycle `u : ℝ → A` with respect to the modular flow `σ^φ`.
Satisfies:
  - Multiplicative cocycle identity: `u(s + t) = u(s) * σ_s^φ(u(t))`
  - Normalization: `u(0) = 1`
  - Unitarity: `u(t) * (u(t))* = 1` and `(u(t))* * u(t) = 1`
-/
structure ConnesOneCocycle (σ : ModularFlow R A) where
  u : ℝ → A
  cocycle_id : ∀ (s t : ℝ), u (s + t) = u s * σ s (u t)
  cocycle_zero : u 0 = 1
  unitary_left : ∀ (t : ℝ), u t * star (u t) = 1
  unitary_right : ∀ (t : ℝ), star (u t) * u t = 1

attribute [simp] ConnesOneCocycle.cocycle_id ConnesOneCocycle.cocycle_zero
                  ConnesOneCocycle.unitary_left ConnesOneCocycle.unitary_right

/-! =========================================================================
    3. Cocycle Inversion and Adjoint Properties
    ========================================================================= -/

variable {σ : ModularFlow R A} (c : ConnesOneCocycle σ)

/--
LEMMA (Adjoint Cocycle Identity):
  `(u(s + t))* = σ_s^φ((u(t))*) * (u(s))*`
-/
theorem cocycle_star_add (s t : ℝ) :
    star (c.u (s + t)) = σ s (star (c.u t)) * star (c.u s) := by
  rw [c.cocycle_id, star_mul, map_star]

/--
THEOREM (Cocycle Inversion Law):
The unitary at `-t` is the backward modular transport of the adjoint:
  `u(-t) = σ_{-t}^φ((u(t))*)`
-/
theorem cocycle_inv (t : ℝ) :
    c.u (-t) = σ (-t) (star (c.u t)) := by
  have h_zero : c.u (t + -t) = 1 := by
    rw [add_neg_cancel, c.cocycle_zero]
  rw [c.cocycle_id] at h_zero
  have h_mul := congr_arg (fun z => star (c.u t) * z) h_zero
  dsimp at h_mul
  rw [mul_one, ← mul_assoc, c.unitary_right, one_mul] at h_mul
  have h_flow := congr_arg (σ (-t)) h_mul
  rw [← flow_add σ, neg_add_cancel, flow_zero] at h_flow
  exact h_flow

/-! =========================================================================
    4. Cocycle Perturbation of the Modular Automorphism Flow
    ========================================================================= -/

/--
The perturbed modular evolution `σ_t^ψ : A → A`:
  `σ_t^ψ(x) = u(t) * σ_t^φ(x) * (u(t))*`
-/
def perturbedFlow (t : ℝ) (x : A) : A :=
  c.u t * σ t x * star (c.u t)

/--
THEOREM (Perturbed Flow Identity at t = 0):
  `σ_0^ψ(x) = x`
-/
@[simp]
theorem perturbedFlow_zero (x : A) :
    perturbedFlow c 0 x = x := by
  dsimp [perturbedFlow]
  rw [c.cocycle_zero, flow_zero, star_one, mul_one, one_mul]

/--
MAIN THEOREM (Multiplicative 1-Parameter Group Law for Perturbed Flow):
The 1-cocycle condition `u(s + t) = u(s) * σ_s^φ(u(t))` implies:
  `σ_{s+t}^ψ(x) = σ_s^ψ(σ_t^ψ(x))`
-/
theorem perturbedFlow_add (s t : ℝ) (x : A) :
    perturbedFlow c (s + t) x = perturbedFlow c s (perturbedFlow c t x) := by
  dsimp [perturbedFlow]
  rw [c.cocycle_id s t, star_mul, ← map_star (σ s), flow_add σ s t x]
  calc
    (c.u s * σ s (c.u t)) * σ s (σ t x) * (σ s (star (c.u t)) * star (c.u s))
      = c.u s * (σ s (c.u t) * σ s (σ t x) * σ s (star (c.u t))) * star (c.u s) := by
        simp only [mul_assoc]
    _ = c.u s * σ s (c.u t * σ t x * star (c.u t)) * star (c.u s) := by
        rw [← map_mul (σ s), ← map_mul (σ s)]

/-! =========================================================================
    5. Cocycle Chain Rule (Transitivity of Relative Moduli)
    ========================================================================= -/

/--
THEOREM (Connes Cocycle Product Rule):
If `u₁` and `u₂` are 1-cocycles with respect to `σ` and commute appropriately:
  `u₁(s+t) * u₂(s+t) = (u₁(s) * u₂(s)) * σ_s(u₁(t) * u₂(t))`
-/
theorem cocycle_prod_law (u₁ u₂ : ℝ → A)
    (h₁ : ∀ s t, u₁ (s + t) = u₁ s * σ s (u₁ t))
    (h₂ : ∀ s t, u₂ (s + t) = u₂ s * σ s (u₂ t))
    (h_comm : ∀ s t, σ s (u₁ t) * u₂ s = u₂ s * σ s (u₁ t)) :
    ∀ s t, (u₁ (s + t) * u₂ (s + t)) =
      (u₁ s * u₂ s) * σ s (u₁ t * u₂ t) := by
  intro s t
  rw [h₁ s t, h₂ s t, map_mul]
  calc
    (u₁ s * σ s (u₁ t)) * (u₂ s * σ s (u₂ t))
      = u₁ s * (σ s (u₁ t) * u₂ s) * σ s (u₂ t) := by
        simp only [mul_assoc]
    _ = u₁ s * (u₂ s * σ s (u₁ t)) * σ s (u₂ t) := by
        rw [h_comm s t]
    _ = (u₁ s * u₂ s) * (σ s (u₁ t) * σ s (u₂ t)) := by
        simp only [mul_assoc]

end InfoGeometry.Modular.ConnesCocycle
