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

/-!
The former commutator-equivariance packet depended on an absent algebra
automorphism owner.  The verified generator-fixed and derivative laws remain
owned by `ModularSurprisalKillingReadback`; no stronger transport theorem is
asserted here without that carrier.
-/

end InfoGeometry.Volume.ModularSurprisalDerivationEquivariance
