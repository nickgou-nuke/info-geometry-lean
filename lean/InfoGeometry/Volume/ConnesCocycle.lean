import InfoGeometry.Volume.RadonNikodym
import InfoGeometry.Krein.DoubledSpace

/-!
# Connes Cocycle Layer

Defines the Connes 1-cocycle identity over a one-parameter automorphism group.
This fuses the multiplicative volume theory with operator algebraic modular dynamics.
-/

namespace InfoGeometry.Volume.ConnesCocycle

open InfoGeometry.Volume.Base
open InfoGeometry.Volume.LogPotential
open InfoGeometry.Volume.RadonNikodym
open InfoGeometry.Krein

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Endomorphisms on the canonical doubled carrier. -/
abbrev AlgebraEnd
    (E : Type _)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] : Type _ :=
  DoubledSpace E →L[ℝ] DoubledSpace E

/--
The Connes 1-Cocycle Identity.
For a modular automorphism group σ and states φ, ψ, the cocycle u satisfies:
u(s+t) = u(s) σ_s(u(t)).
Ensures σ is a homomorphism from (ℝ, +) to Aut(AlgebraEnd H).
-/
def IsConnesCocycle
    (σ : ℝ →* (AlgebraEnd H ≃ₐ[ℝ] AlgebraEnd H))
    (u : ℝ → AlgebraEnd H) : Prop :=
  ∀ s t : ℝ, u (s + t) = (u s) * (σ s (u t))

/--
Constructive scalar bridge from operator cocycles to real multiplicative cocycles.

`toScalar` is the scalar observable, and `sigma_invariant` enforces compatibility
with the modular action.
-/
structure ScalarCocycleBridge
    (σ : ℝ →* (AlgebraEnd H ≃ₐ[ℝ] AlgebraEnd H)) where
  toScalar : AlgebraEnd H →* ℝˣ
  sigma_invariant : ∀ s A, toScalar (σ s A) = toScalar A

/--
Scalar cocycle induced from an operator cocycle via a scalar bridge.
-/
noncomputable def scalarCocycle
    (σ : ℝ →* (AlgebraEnd H ≃ₐ[ℝ] AlgebraEnd H))
    (u : ℝ → AlgebraEnd H)
    (B : ScalarCocycleBridge (H := H) σ) : ℝ → ℝˣ :=
  fun t => B.toScalar (u t)

/--
Multiplicative cocycle law for the induced scalar cocycle.
-/
theorem scalarCocycle_mul
    (σ : ℝ →* (AlgebraEnd H ≃ₐ[ℝ] AlgebraEnd H))
    (u : ℝ → AlgebraEnd H)
    (hCocycle : IsConnesCocycle σ u)
    (B : ScalarCocycleBridge (H := H) σ) :
    ∀ s t : ℝ,
      scalarCocycle (H := H) σ u B (s + t)
        = scalarCocycle (H := H) σ u B s * scalarCocycle (H := H) σ u B t := by
  intro s t
  unfold scalarCocycle
  calc
    B.toScalar (u (s + t))
        = B.toScalar ((u s) * (σ s (u t))) := by rw [hCocycle s t]
    _ = B.toScalar (u s) * B.toScalar (σ s (u t)) := by
          rw [B.toScalar.map_mul]
    _ = B.toScalar (u s) * B.toScalar (u t) := by
          rw [B.sigma_invariant s (u t)]

/--
Additive cocycle potential induced from the scalar cocycle by logarithm.
-/
noncomputable def cocycleLogPotential
    (σ : ℝ →* (AlgebraEnd H ≃ₐ[ℝ] AlgebraEnd H))
    (u : ℝ → AlgebraEnd H)
    (B : ScalarCocycleBridge (H := H) σ) : ℝ → ℝ :=
  fun t => Real.log |((scalarCocycle (H := H) σ u B t : ℝˣ) : ℝ)|

/--
Additivity of the logarithmic cocycle potential.
-/
theorem cocycleLogPotential_add
    (σ : ℝ →* (AlgebraEnd H ≃ₐ[ℝ] AlgebraEnd H))
    (u : ℝ → AlgebraEnd H)
    (hCocycle : IsConnesCocycle σ u)
    (B : ScalarCocycleBridge (H := H) σ) :
    ∀ s t : ℝ,
      cocycleLogPotential (H := H) σ u B (s + t)
        = cocycleLogPotential (H := H) σ u B s
          + cocycleLogPotential (H := H) σ u B t := by
  intro s t
  have hmul :
      scalarCocycle (H := H) σ u B (s + t)
        = scalarCocycle (H := H) σ u B s * scalarCocycle (H := H) σ u B t :=
    scalarCocycle_mul (H := H) σ u hCocycle B s t
  have hmulVal :
      ((scalarCocycle (H := H) σ u B (s + t) : ℝˣ) : ℝ)
        =
      ((scalarCocycle (H := H) σ u B s : ℝˣ) : ℝ)
        * ((scalarCocycle (H := H) σ u B t : ℝˣ) : ℝ) := by
    exact congrArg (fun z : ℝˣ => (z : ℝ)) hmul
  unfold cocycleLogPotential
  rw [hmulVal, abs_mul, Real.log_mul]
  · exact abs_ne_zero.mpr (Units.ne_zero _)
  · exact abs_ne_zero.mpr (Units.ne_zero _)

/--
Theorem: The Log-Cocycle generates an Additive Potential.
In the Type III context, the derivative of the Connes cocycle recovers 
the relative entropy / modular Hamiltonian.
-/
theorem cocycle_additive_potential
    (σ : ℝ →* (AlgebraEnd H ≃ₐ[ℝ] AlgebraEnd H))
    (u : ℝ → AlgebraEnd H)
    (hCocycle : IsConnesCocycle σ u)
    (B : ScalarCocycleBridge (H := H) σ) :
    ∃ (Φ : ℝ → ℝ), ∀ s t, Φ (s + t) = Φ s + Φ t :=
  ⟨cocycleLogPotential (H := H) σ u B,
    cocycleLogPotential_add (H := H) σ u hCocycle B⟩

end InfoGeometry.Volume.ConnesCocycle
