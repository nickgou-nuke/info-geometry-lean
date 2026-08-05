import Mathlib

namespace InfoGeometry.Physics

/-!
The GENERIC rate laws are stated directly from their hypotheses.  No
structure pretends to construct a Poisson or Onsager operator: those
state-dependent operators, their symmetries, positivity, and degeneracy are
explicit inputs to the theorems below.
-/

variable {State : Type*} {Tangent : State → Type*}
variable [∀ ρ, AddCommGroup (Tangent ρ)] [∀ ρ, Module ℝ (Tangent ρ)]

def metriplecticVelocity
    (poissonOperator onsagerOperator :
      ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ)
    (energyGradient entropyGradient : ∀ ρ, Tangent ρ)
    (ρ : State) : Tangent ρ :=
  poissonOperator ρ (energyGradient ρ) +
    onsagerOperator ρ (entropyGradient ρ)

def energyRate
    (pairing : ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ →ₗ[ℝ] ℝ)
    (poissonOperator onsagerOperator :
      ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ)
    (energyGradient entropyGradient : ∀ ρ, Tangent ρ)
    (ρ : State) : ℝ :=
  pairing ρ (energyGradient ρ)
    (metriplecticVelocity poissonOperator onsagerOperator
      energyGradient entropyGradient ρ)

def entropyRate
    (pairing : ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ →ₗ[ℝ] ℝ)
    (poissonOperator onsagerOperator :
      ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ)
    (energyGradient entropyGradient : ∀ ρ, Tangent ρ)
    (ρ : State) : ℝ :=
  pairing ρ (entropyGradient ρ)
    (metriplecticVelocity poissonOperator onsagerOperator
      energyGradient entropyGradient ρ)

theorem energy_conserved
    (pairing : ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ →ₗ[ℝ] ℝ)
    (pairing_symm : ∀ ρ X Y, pairing ρ X Y = pairing ρ Y X)
    (poissonOperator onsagerOperator :
      ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ)
    (poisson_skew : ∀ ρ X Y,
      pairing ρ (poissonOperator ρ X) Y =
        -pairing ρ X (poissonOperator ρ Y))
    (onsager_symmetric : ∀ ρ X Y,
      pairing ρ (onsagerOperator ρ X) Y =
        pairing ρ X (onsagerOperator ρ Y))
    (energyGradient entropyGradient : ∀ ρ, Tangent ρ)
    (energy_degenerate : ∀ ρ,
      onsagerOperator ρ (energyGradient ρ) = 0)
    (ρ : State) :
    energyRate pairing poissonOperator onsagerOperator
        energyGradient entropyGradient ρ = 0 := by
  dsimp [energyRate, metriplecticVelocity]
  rw [LinearMap.map_add]
  have hJ :
      pairing ρ (energyGradient ρ)
        (poissonOperator ρ (energyGradient ρ)) = 0 := by
    have hskew := poisson_skew ρ (energyGradient ρ) (energyGradient ρ)
    have hswap := pairing_symm ρ
      (poissonOperator ρ (energyGradient ρ)) (energyGradient ρ)
    rw [hswap] at hskew
    linarith
  have hM :
      pairing ρ (energyGradient ρ)
        (onsagerOperator ρ (entropyGradient ρ)) = 0 := by
    rw [← onsager_symmetric ρ (energyGradient ρ) (entropyGradient ρ)]
    rw [energy_degenerate ρ]
    simp
  simp [hJ, hM]

theorem entropy_nondecreasing
    (pairing : ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ →ₗ[ℝ] ℝ)
    (pairing_symm : ∀ ρ X Y, pairing ρ X Y = pairing ρ Y X)
    (poissonOperator onsagerOperator :
      ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ)
    (poisson_skew : ∀ ρ X Y,
      pairing ρ (poissonOperator ρ X) Y =
        -pairing ρ X (poissonOperator ρ Y))
    (energyGradient entropyGradient : ∀ ρ, Tangent ρ)
    (onsager_nonnegative : ∀ ρ X,
      0 ≤ pairing ρ X (onsagerOperator ρ X))
    (entropy_casimir : ∀ ρ,
      poissonOperator ρ (entropyGradient ρ) = 0)
    (ρ : State) :
    0 ≤ entropyRate pairing poissonOperator onsagerOperator
        energyGradient entropyGradient ρ := by
  dsimp [entropyRate, metriplecticVelocity]
  rw [LinearMap.map_add]
  have hJ :
      pairing ρ (entropyGradient ρ)
        (poissonOperator ρ (energyGradient ρ)) = 0 := by
    have hsymm := pairing_symm ρ (entropyGradient ρ)
      (poissonOperator ρ (energyGradient ρ))
    rw [hsymm]
    have hskew := poisson_skew ρ (energyGradient ρ) (entropyGradient ρ)
    rw [hskew, entropy_casimir ρ]
    simp
  rw [hJ, zero_add]
  exact onsager_nonnegative ρ (entropyGradient ρ)

end InfoGeometry.Physics
