import InfoGeometry.Canonical.PhysicalBdGPairingBridgeComplex
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Tactic

/-!
# Native conjugate-linear particle-hole symmetry for the BdG block

This owner complements the complex-linear proxy by using Mathlib's native
continuous conjugate-linear maps.  The hypotheses are pointwise block
intertwining identities; no antiunitarity or involutivity is assumed unless
it is explicitly supplied.
-/

noncomputable section

namespace InfoGeometry.Canonical.PhysicalBdGPairingBridgeAntiLinear

open ContinuousLinearMap
open InfoGeometry.Canonical.PhysicalBdGPairingBridgeComplex

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H
local notation "AntiEndH" => H →L⋆[ℂ] H
local notation "NambuH" => H × H

/-- The native conjugate-linear Nambu sheet swap. -/
noncomputable def PHS_operator (C₀ : AntiEndH) : NambuH →L⋆[ℂ] NambuH where
  toFun := fun ψ => (C₀ ψ.2, C₀ ψ.1)
  map_add' ψ φ := by
    ext <;> simp
  map_smul' z ψ := by
    ext <;> simp
  cont := by
    fun_prop

@[simp] theorem PHS_operator_apply (C₀ : AntiEndH) (u v : H) :
    PHS_operator C₀ (u, v) = (C₀ v, C₀ u) := rfl

/-- An involutive one-particle conjugation gives an involutive Nambu map. -/
theorem PHS_operator_sq
    (C₀ : AntiEndH)
    (hC₀ : ∀ x : H, C₀ (C₀ x) = x)
    (ψ : NambuH) :
    PHS_operator C₀ (PHS_operator C₀ ψ) = ψ := by
  rcases ψ with ⟨u, v⟩
  simp [hC₀]

/-! ## Bundled anti-linear equivalence -/

/--
The involutive particle-hole map as a native continuous star-linear
equivalence.  The same map supplies both inverse directions.
-/
noncomputable def PHS_operator_equiv
    (C₀ : AntiEndH)
    (hC₀ : ∀ x : H, C₀ (C₀ x) = x) :
    NambuH ≃L⋆[ℂ] NambuH where
  toLinearEquiv :=
    { toFun := PHS_operator C₀
      invFun := PHS_operator C₀
      map_add' := (PHS_operator C₀).map_add
      map_smul' := by
        intro z ψ
        exact map_smulₛₗ (PHS_operator C₀) z ψ
      left_inv := by
        intro ψ
        exact PHS_operator_sq C₀ hC₀ ψ
      right_inv := by
        intro ψ
        exact PHS_operator_sq C₀ hC₀ ψ }
  continuous_toFun := (PHS_operator C₀).continuous
  continuous_invFun := (PHS_operator C₀).continuous

@[simp] theorem PHS_operator_equiv_apply
    (C₀ : AntiEndH)
    (hC₀ : ∀ x : H, C₀ (C₀ x) = x)
    (ψ : NambuH) :
    PHS_operator_equiv C₀ hC₀ ψ = PHS_operator C₀ ψ := by
  simp [PHS_operator_equiv]

@[simp] theorem PHS_operator_equiv_symm_apply
    (C₀ : AntiEndH)
    (hC₀ : ∀ x : H, C₀ (C₀ x) = x)
    (ψ : NambuH) :
    (PHS_operator_equiv C₀ hC₀).symm ψ = PHS_operator C₀ ψ := by
  apply (PHS_operator_equiv C₀ hC₀).injective
  rw [(PHS_operator_equiv C₀ hC₀).apply_symm_apply]
  rw [PHS_operator_equiv_apply]
  exact (PHS_operator_sq C₀ hC₀ ψ).symm

/-- Pointwise anti-linear BdG particle-hole symmetry. -/
theorem bdg_particle_hole_symmetry
    (h Δ : EndH)
    (C₀ : AntiEndH)
    (h_comm_adjoint : ∀ x : H,
      C₀ (ContinuousLinearMap.adjoint h x) = h (C₀ x))
    (h_anti_adjoint : ∀ x : H,
      C₀ (ContinuousLinearMap.adjoint Δ x) = -Δ (C₀ x))
    (h_comm : ∀ x : H,
      C₀ (h x) = ContinuousLinearMap.adjoint h (C₀ x))
    (h_anti : ∀ x : H,
      C₀ (Δ x) = -ContinuousLinearMap.adjoint Δ (C₀ x))
    (ψ : NambuH) :
    PHS_operator C₀ (H_BdG h Δ ψ) =
      -(H_BdG h Δ (PHS_operator C₀ ψ)) := by
  rcases ψ with ⟨u, v⟩
  apply Prod.ext
  · simp only [H_BdG_apply, PHS_operator_apply, Prod.fst_neg]
    rw [map_sub, h_anti_adjoint u, h_comm_adjoint v]
    abel
  · simp only [H_BdG_apply, PHS_operator_apply, Prod.snd_neg]
    rw [map_add, h_comm u, h_anti v]
    abel

/-- The reverse intertwining laws follow from the first pair and `C₀² = 1`. -/
theorem conjugation_comm_reverse
    (h : EndH) (C₀ : AntiEndH)
    (hC₀ : ∀ x : H, C₀ (C₀ x) = x)
    (h_comm_adjoint : ∀ x : H,
      C₀ (ContinuousLinearMap.adjoint h x) = h (C₀ x))
    (x : H) :
    C₀ (h x) = ContinuousLinearMap.adjoint h (C₀ x) := by
  have hx := congrArg C₀ (h_comm_adjoint (C₀ x))
  have hx' : ContinuousLinearMap.adjoint h (C₀ x) = C₀ (h x) := by
    simpa [hC₀] using hx
  exact hx'.symm

theorem conjugation_anti_reverse
    (Δ : EndH) (C₀ : AntiEndH)
    (hC₀ : ∀ x : H, C₀ (C₀ x) = x)
    (h_anti_adjoint : ∀ x : H,
      C₀ (ContinuousLinearMap.adjoint Δ x) = -Δ (C₀ x))
    (x : H) :
    C₀ (Δ x) = -ContinuousLinearMap.adjoint Δ (C₀ x) := by
  have hx := congrArg C₀ (h_anti_adjoint (C₀ x))
  have hx' : ContinuousLinearMap.adjoint Δ (C₀ x) = -C₀ (Δ x) := by
    simpa [hC₀] using hx
  have hneg := congrArg Neg.neg hx'
  simpa using hneg.symm

/-- PHS from involutivity and only the forward block intertwining laws. -/
theorem bdg_particle_hole_symmetry_of_involutive
    (h Δ : EndH) (C₀ : AntiEndH)
    (hC₀ : ∀ x : H, C₀ (C₀ x) = x)
    (h_comm_adjoint : ∀ x : H,
      C₀ (ContinuousLinearMap.adjoint h x) = h (C₀ x))
    (h_anti_adjoint : ∀ x : H,
      C₀ (ContinuousLinearMap.adjoint Δ x) = -Δ (C₀ x))
    (ψ : NambuH) :
    PHS_operator C₀ (H_BdG h Δ ψ) =
      -(H_BdG h Δ (PHS_operator C₀ ψ)) := by
  exact bdg_particle_hole_symmetry h Δ C₀ h_comm_adjoint
    h_anti_adjoint
    (conjugation_comm_reverse h C₀ hC₀ h_comm_adjoint)
    (conjugation_anti_reverse Δ C₀ hC₀ h_anti_adjoint) ψ

end InfoGeometry.Canonical.PhysicalBdGPairingBridgeAntiLinear

end noncomputable section
