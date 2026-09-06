import InfoGeometry.Volume.ConnesInfinitesimal
import InfoGeometry.Volume.ModularSurprisalKillingReadback

/-!
# Modular surprisal derivation equivariance

This owner records the fundamental equivariance of the modular derivation
with respect to the modular flow.  The modular surprisal generator
`K = -log Δ` generates an inner derivation

  δ_K(A) = [K, A]

and the modular flow

  α_t(A) = e^{tK} A e^{-tK}

satisfies

  α_t ∘ δ_K = δ_K ∘ α_t.

Equivalently, the transported commutator equals the commutator with the
transported generator:

  α_t([K, A]) = [K, α_t(A)].

This is the precise statement that the modular automorphism preserves its
own infinitesimal generator.
-/

namespace InfoGeometry.Volume.ModularSurprisalDerivationEquivariance

open InfoGeometry.Volume.ConnesInfinitesimal
open InfoGeometry.Volume.ModularSurprisalKillingReadback
open InfoGeometry.Volume.ConnesCocycle

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The modular flow fixes the generator itself. -/
theorem modular_flow_fixes_generator (K : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction K K t = K :=
  modularHamiltonianAction_self K t

/-- The infinitesimal modular action on the generator vanishes. -/
theorem modular_derivation_of_generator_zero (K : AlgebraEnd H) :
    ⁅K, K⁆ = 0 := by simp

/-- The modular flow commutes with its own derivation.

This is the core equivariance theorem: the transported commutator equals
the commutator with the transported generator.
-/
theorem modular_derivation_equivariant
    (K A : AlgebraEnd H) (t : ℝ) :
    modularHamiltonianAction K ⁅K, A⁆ t =
      ⁅K, modularHamiltonianAction K A t⁆ := by
  exact modular_surprisal_flow_commutes_with_derivation K A t

/-- Additive parameter version: the equivariance is symmetric in the
flow parameters when applied to the modular derivation. -/
theorem modular_derivation_equivariant_add
    (K A : AlgebraEnd H) (s t : ℝ) :
    modularHamiltonianAction K (modularHamiltonianAction K ⁅K, A⁆ s) t =
      modularHamiltonianAction K (modularHamiltonianAction K ⁅K, A⁆ t) s := by
  calc
    modularHamiltonianAction K (modularHamiltonianAction K ⁅K, A⁆ s) t =
        modularHamiltonianAction K ⁅K, A⁆ (t + s) :=
      (modularHamiltonianAction_add K ⁅K, A⁆ t s).symm
    _ = modularHamiltonianAction K ⁅K, A⁆ (s + t) := by rw [add_comm]
    _ = modularHamiltonianAction K (modularHamiltonianAction K ⁅K, A⁆ t) s :=
      modularHamiltonianAction_add K ⁅K, A⁆ s t

theorem modular_flow_fixes_generator_pow
    (K : AlgebraEnd H) (n : ℕ) (t : ℝ) :
    modularHamiltonianAction K (K ^ n) t = K ^ n := by
  rw [modularHamiltonianAction_pow, modular_flow_fixes_generator]

theorem modular_flow_fixes_generator_smul
    (K : AlgebraEnd H) (r t : ℝ) :
    modularHamiltonianAction K (r • K) t = r • K := by
  rw [modularHamiltonianAction_smul, modular_flow_fixes_generator]

end InfoGeometry.Volume.ModularSurprisalDerivationEquivariance
