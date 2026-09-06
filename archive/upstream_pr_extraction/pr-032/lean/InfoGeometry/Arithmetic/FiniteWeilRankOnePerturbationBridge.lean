import Mathlib
import InfoGeometry.Arithmetic.FiniteWeilMangoldtQuadraticFormBridge

/-!
# Finite rank-one perturbations for the Weil shadow

This owner stays at the bounded finite-operator level.  It defines the
rank-one operator used in the usual perturbation formula and proves its basic
linearity/evaluation laws, together with self-adjointness in the symmetric
`|ξ⟩⟨ξ|` case.  No unbounded perturbation theorem, quotient by a radical, or
spectral convergence statement is asserted.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.FiniteWeilRankOnePerturbationBridge

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Rank-one operator `f ↦ ⟪η,f⟫ ξ`. -/
def rankOneOperator (ξ η : H) : H →ₗ[ℂ] H where
  toFun f := ⟪η, f⟫_ℂ • ξ
  map_add' f g := by rw [inner_add_right, add_smul]
  map_smul' c f := by
    rw [inner_smul_right, smul_smul]
    rfl

@[simp] theorem rankOneOperator_apply (ξ η f : H) :
    rankOneOperator ξ η f = ⟪η, f⟫_ℂ • ξ := rfl

theorem rankOneOperator_selfAdjoint (ξ f g : H) :
    ⟪f, rankOneOperator ξ ξ g⟫_ℂ =
      ⟪rankOneOperator ξ ξ f, g⟫_ℂ := by
  simp only [rankOneOperator_apply, inner_smul_right, inner_smul_left]
  rw [inner_conj_symm]
  ring

/-- Subtract a rank-one perturbation from a supplied bounded operator. -/
def rankOnePerturbation (D : H →ₗ[ℂ] H) (ξ η : H) : H →ₗ[ℂ] H :=
  D - rankOneOperator ξ η

@[simp] theorem rankOnePerturbation_apply
    (D : H →ₗ[ℂ] H) (ξ η f : H) :
    rankOnePerturbation D ξ η f =
      D f - ⟪η, f⟫_ℂ • ξ := by
  simp [rankOnePerturbation]

theorem rankOnePerturbation_eq_sub_rankOne
    (D : H →ₗ[ℂ] H) (ξ η : H) :
    rankOnePerturbation D ξ η = D - rankOneOperator ξ η := rfl

theorem rankOnePerturbation_selfAdjoint
    (D : H →ₗ[ℂ] H)
    (hD : ∀ f g, ⟪f, D g⟫_ℂ = ⟪D f, g⟫_ℂ)
    (ξ f g : H) :
    ⟪f, rankOnePerturbation D ξ ξ g⟫_ℂ =
      ⟪rankOnePerturbation D ξ ξ f, g⟫_ℂ := by
  simp only [rankOnePerturbation, LinearMap.sub_apply, inner_sub_right,
    inner_sub_left]
  rw [hD f g, rankOneOperator_selfAdjoint ξ f g]


end InfoGeometry.Arithmetic.FiniteWeilRankOnePerturbationBridge
