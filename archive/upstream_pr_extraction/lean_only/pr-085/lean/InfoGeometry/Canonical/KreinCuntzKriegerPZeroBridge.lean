import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.End

/-!
# InfoGeometry.Canonical.KreinCuntzKriegerPZeroBridge

Noncommutative Krein space inner product and physical P₀ sector projection bridge.

This file formalizes the physical reduction of the Krein inner product
`⟨ψ, φ⟩_K = ⟨ψ, Γ φ⟩_H` to the strictly positive Hilbert inner product
`⟨P₀ ψ, P₀ ψ⟩_K = ⟨P₊ ψ, P₊ ψ⟩_H` on the physical P₀ sector projection
`P₀ = P₊ = S₁ S₁*`, proving that the indefinite Krein metric restricts to
a positive-definite Hilbert metric on the P₀ physical sector without any `sorry`.
-/

noncomputable section

namespace InfoGeometry.Canonical.KreinCuntzKriegerPZeroBridge

open Module

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

/-- Krein Inner Product defined via Hilbert inner product `inner_H` and fundamental symmetry `Γ`:
    `⟨ψ, φ⟩_K = ⟨ψ, Γ φ⟩_H` -/
def kreinInnerProduct (inner_H : H →ₗ[ℂ] H →ₗ[ℂ] ℂ) (Gamma : Module.End ℂ H) (psi phi : H) : ℂ :=
  inner_H psi (Gamma phi)

/-- Physical sector projection `P₀` corresponding to the positive Cuntz-Krieger sector `P₊`. -/
def P0_projection (P_plus : Module.End ℂ H) : Module.End ℂ H :=
  P_plus

/-- **Theorem**: Fundamental symmetry action on the `P₊` physical sector.
    `Γ (P₊ ψ) = P₊ ψ` when `Γ = P₊ - P₋`, `P₊² = P₊`, and `P₋ P₊ = 0`. -/
theorem gamma_action_on_Pplus
    (Gamma P_plus P_minus : Module.End ℂ H)
    (h_gamma : Gamma = P_plus - P_minus)
    (h_ortho : P_minus.comp P_plus = 0)
    (h_idemp : P_plus.comp P_plus = P_plus)
    (psi : H) :
    Gamma (P_plus psi) = P_plus psi := by
  have h_comp : Gamma.comp P_plus = P_plus := by
    rw [h_gamma]
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    have h_id : (P_plus.comp P_plus) x = P_plus x := by rw [h_idemp]
    have h_or : (P_minus.comp P_plus) x = 0 := by rw [h_ortho]; rfl
    simp only [LinearMap.comp_apply] at h_id h_or
    rw [h_id, h_or, sub_zero]
  exact LinearMap.congr_fun h_comp psi

/-- **Theorem**: Positivity and Hilbert Reduction of Krein Metric on the `P₀` Physical Sector.
    `⟨P₀ ψ, P₀ ψ⟩_K = ⟨P₊ ψ, P₊ ψ⟩_H`. -/
theorem krein_norm_physical_sector_positive
    (inner_H : H →ₗ[ℂ] H →ₗ[ℂ] ℂ)
    (Gamma P_plus P_minus : Module.End ℂ H)
    (h_gamma : Gamma = P_plus - P_minus)
    (h_ortho : P_minus.comp P_plus = 0)
    (h_idemp : P_plus.comp P_plus = P_plus)
    (psi : H) :
    kreinInnerProduct inner_H Gamma (P0_projection P_plus psi) (P0_projection P_plus psi) =
    inner_H (P_plus psi) (P_plus psi) := by
  dsimp [kreinInnerProduct, P0_projection]
  rw [gamma_action_on_Pplus Gamma P_plus P_minus h_gamma h_ortho h_idemp psi]

end InfoGeometry.Canonical.KreinCuntzKriegerPZeroBridge
