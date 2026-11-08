import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Yang–Baxter Quotient Descent

If linear maps σ₁, σ₂ satisfy YBE upstairs and preserve a relation
submodule R, then the descended maps σ̄₁, σ̄₂ on V⧸R also satisfy YBE.

Uses `Submodule.mapQ` from mathlib.
-/

noncomputable section

namespace YangBaxterQuotientDescent

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable (R : Submodule K V)

/-- If `f` preserves `R`, it descends via `Submodule.mapQ`. -/
def desc (f : V →ₗ[K] V) (h : R ≤ Submodule.comap f R) : (V ⧸ R) →ₗ[K] (V ⧸ R) :=
  Submodule.mapQ R R f h

/-- `desc` commutes with the quotient projection. -/
theorem desc_mk (f : V →ₗ[K] V) (h : R ≤ Submodule.comap f R) (x : V) :
    desc R f h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := by
  dsimp [desc]

/-- Pointwise YBE: for all y, σ₁(σ₂(σ₁(y))) = σ₂(σ₁(σ₂(y))). -/
lemma ybe_pointwise (σ₁ σ₂ : V →ₗ[K] V) (hYBE : σ₁ ∘ₗ σ₂ ∘ₗ σ₁ = σ₂ ∘ₗ σ₁ ∘ₗ σ₂) (y : V) :
    σ₁ (σ₂ (σ₁ y)) = σ₂ (σ₁ (σ₂ y)) := by
  have h := LinearMap.congr_fun hYBE y
  simpa [LinearMap.comp_apply] using h

/-- Descended maps agree on generators: both sides applied to `mk y` are equal. -/
lemma descended_agree_on_generators
    (σ₁ σ₂ : V →ₗ[K] V)
    (h₁ : R ≤ Submodule.comap σ₁ R) (h₂ : R ≤ Submodule.comap σ₂ R)
    (hYBE : σ₁ ∘ₗ σ₂ ∘ₗ σ₁ = σ₂ ∘ₗ σ₁ ∘ₗ σ₂) (y : V) :
    (desc R σ₁ h₁ ∘ₗ desc R σ₂ h₂ ∘ₗ desc R σ₁ h₁) (Submodule.Quotient.mk y) =
    (desc R σ₂ h₂ ∘ₗ desc R σ₁ h₁ ∘ₗ desc R σ₂ h₂) (Submodule.Quotient.mk y) := by
  simp [desc, LinearMap.comp_apply, ybe_pointwise σ₁ σ₂ hYBE]

/-- YBE descends: if σ₁, σ₂ preserve R and satisfy YBE upstairs,
then their descents also satisfy YBE downstairs. -/
theorem yang_baxter_descends
    (σ₁ σ₂ : V →ₗ[K] V)
    (h₁ : R ≤ Submodule.comap σ₁ R) (h₂ : R ≤ Submodule.comap σ₂ R)
    (hYBE : σ₁ ∘ₗ σ₂ ∘ₗ σ₁ = σ₂ ∘ₗ σ₁ ∘ₗ σ₂) :
    desc R σ₁ h₁ ∘ₗ desc R σ₂ h₂ ∘ₗ desc R σ₁ h₁ =
    desc R σ₂ h₂ ∘ₗ desc R σ₁ h₁ ∘ₗ desc R σ₂ h₂ := by
  refine LinearMap.ext (fun x => ?_)
  rcases Submodule.Quotient.mk_surjective R x with ⟨y, hy⟩
  rw [← hy]
  exact descended_agree_on_generators R σ₁ σ₂ h₁ h₂ hYBE y

#check yang_baxter_descends

end YangBaxterQuotientDescent
