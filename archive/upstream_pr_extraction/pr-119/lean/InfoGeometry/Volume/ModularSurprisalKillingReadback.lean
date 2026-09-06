import InfoGeometry.Volume.ModularSurprisalDerivationBridge

/-!
# Modular surprisal generator readback

This file exposes the already-proved operatorial modular facts under names
useful to the surprisal/derivation lane.  It does not identify the modular
generator with a Killing form; that requires a separate Lie-algebra datum.
-/

noncomputable section

namespace InfoGeometry.Volume.ModularSurprisalKillingReadback

open InfoGeometry.Volume.ConnesInfinitesimal
open InfoGeometry.Volume.ConnesCocycle
open InfoGeometry.Canonical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-! ## Generator self-invariance and infinitesimal readback -/

theorem modular_generator_preserved
    (K : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction (H := H) K K t = K := by
  exact modularHamiltonianAction_self K t

theorem modular_generator_commutator_zero
    (K : AlgebraEnd H) :
    ⁅K, K⁆ = 0 := by
  simp

theorem modular_generator_has_zero_derivation_on_self
    (K : AlgebraEnd H) :
    HasDerivAt
      (fun t : ℝ => modularHamiltonianAction (H := H) K K t)
      0 0 := by
  exact modularHamiltonianAction_hasDerivAt_zero_self K

theorem modular_generator_power_preserved
    (K : AlgebraEnd H) (n : ℕ) (t : ℝ) :
    modularHamiltonianAction (H := H) K (K ^ n) t = K ^ n := by
  rw [modularHamiltonianAction_pow]
  rw [modular_generator_preserved]

/-! ## General commutator-generated modular derivation -/

theorem modular_surprisal_flow_derivative
    (K A : AlgebraEnd H) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => modularHamiltonianAction (H := H) K A s)
      (modularHamiltonianAction (H := H) K ⁅K, A⁆ t)
      t := by
  exact modularHamiltonianAction_hasDerivAt K A t

theorem modular_surprisal_flow_preserves_commutator
    (K A B : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction (H := H) K ⁅A, B⁆ t =
      ⁅modularHamiltonianAction (H := H) K A t,
        modularHamiltonianAction (H := H) K B t⁆ := by
  exact modularHamiltonianAction_lie K A B t

theorem modular_surprisal_flow_commutes_with_derivation
    (K A : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction (H := H) K ⁅K, A⁆ t =
      ⁅K, modularHamiltonianAction (H := H) K A t⁆ := by
  simpa using
    (modularHamiltonianAction_lie (H := H) K K A t)

noncomputable def modular_surprisal_flow_is_algebra_equiv
    (K : AlgebraEnd H) (t : ℝ) :
    AlgebraEnd H ≃ₐ[ℝ] AlgebraEnd H :=
  modularHamiltonianActionAlgEquiv K t

end InfoGeometry.Volume.ModularSurprisalKillingReadback
