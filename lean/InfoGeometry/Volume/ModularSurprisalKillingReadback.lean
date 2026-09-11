import InfoGeometry.Volume.ModularSurprisalDerivationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

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
  apply modularHamiltonianAction_eq_self_of_commute K (K ^ n) t
  exact ((Commute.refl K).pow_right n).symm

/-! ## General commutator-generated modular derivation -/

theorem modular_surprisal_flow_derivative
    (K A : AlgebraEnd H) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => modularHamiltonianAction (H := H) K A s)
      (modularHamiltonianAction (H := H) K ⁅K, A⁆ t)
      t := by
  exact modularHamiltonianAction_hasDerivAt K A t

end InfoGeometry.Volume.ModularSurprisalKillingReadback
