import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

theorem metriplecticVelocity_eq_zero_of_degenerate
    (poissonOperator onsagerOperator :
      ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ)
    (energyGradient entropyGradient : ∀ ρ, Tangent ρ)
    (ρ : State)
    (hP : poissonOperator ρ (energyGradient ρ) = 0)
    (hM : onsagerOperator ρ (entropyGradient ρ) = 0) :
    metriplecticVelocity poissonOperator onsagerOperator
      energyGradient entropyGradient ρ = 0 := by
  dsimp [metriplecticVelocity]
  rw [hP, hM]
  exact add_zero 0

theorem metriplectic_stationary_rates
    (pairing : ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ →ₗ[ℝ] ℝ)
    (poissonOperator onsagerOperator :
      ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ)
    (energyGradient entropyGradient : ∀ ρ, Tangent ρ)
    (ρ : State)
    (hstationary :
      metriplecticVelocity poissonOperator onsagerOperator
        energyGradient entropyGradient ρ = 0) :
    energyRate pairing poissonOperator onsagerOperator
        energyGradient entropyGradient ρ = 0 ∧
    entropyRate pairing poissonOperator onsagerOperator
        energyGradient entropyGradient ρ = 0 := by
  constructor
  · simp [energyRate, hstationary]
  · simp [entropyRate, hstationary]

theorem entropyRate_eq_zero_of_degenerate
    (pairing : ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ →ₗ[ℝ] ℝ)
    (poissonOperator onsagerOperator :
      ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ)
    (energyGradient entropyGradient : ∀ ρ, Tangent ρ)
    (ρ : State)
    (hP : poissonOperator ρ (energyGradient ρ) = 0)
    (hM : onsagerOperator ρ (entropyGradient ρ) = 0) :
    entropyRate pairing poissonOperator onsagerOperator
      energyGradient entropyGradient ρ = 0 := by
  dsimp [entropyRate, metriplecticVelocity]
  rw [hP, hM]
  simp

theorem entropyRate_eq_onsager_quadratic
    (pairing : ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ →ₗ[ℝ] ℝ)
    (pairing_symm : ∀ ρ X Y, pairing ρ X Y = pairing ρ Y X)
    (poissonOperator onsagerOperator :
      ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ)
    (poisson_skew : ∀ ρ X Y,
      pairing ρ (poissonOperator ρ X) Y =
        -pairing ρ X (poissonOperator ρ Y))
    (energyGradient entropyGradient : ∀ ρ, Tangent ρ)
    (entropy_casimir : ∀ ρ,
      poissonOperator ρ (entropyGradient ρ) = 0)
    (ρ : State) :
    entropyRate pairing poissonOperator onsagerOperator
        energyGradient entropyGradient ρ =
      pairing ρ (entropyGradient ρ)
        (onsagerOperator ρ (entropyGradient ρ)) := by
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

theorem casimir_conserved
    (pairing : ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ →ₗ[ℝ] ℝ)
    (poissonOperator onsagerOperator :
      ∀ ρ, Tangent ρ →ₗ[ℝ] Tangent ρ)
    (energyGradient entropyGradient casimirGradient : ∀ ρ, Tangent ρ)
    (poisson_casimir : ∀ ρ,
      poissonOperator ρ (casimirGradient ρ) = 0)
    (onsager_casimir : ∀ ρ,
      onsagerOperator ρ (casimirGradient ρ) = 0)
    (pairing_symm : ∀ ρ X Y, pairing ρ X Y = pairing ρ Y X)
    (poisson_skew : ∀ ρ X Y,
      pairing ρ (poissonOperator ρ X) Y =
        -pairing ρ X (poissonOperator ρ Y))
    (onsager_symmetric : ∀ ρ X Y,
      pairing ρ (onsagerOperator ρ X) Y =
        pairing ρ X (onsagerOperator ρ Y))
    (ρ : State) :
    pairing ρ (casimirGradient ρ)
      (metriplecticVelocity poissonOperator onsagerOperator
        energyGradient entropyGradient ρ) = 0 := by
  dsimp [metriplecticVelocity]
  rw [LinearMap.map_add]
  have hJ :
      pairing ρ (casimirGradient ρ)
        (poissonOperator ρ (energyGradient ρ)) = 0 := by
    rw [pairing_symm]
    rw [poisson_skew]
    rw [poisson_casimir]
    simp
  have hM :
      pairing ρ (casimirGradient ρ)
        (onsagerOperator ρ (entropyGradient ρ)) = 0 := by
    rw [← onsager_symmetric]
    rw [onsager_casimir]
    simp
  simp [hJ, hM]

noncomputable def symmetricPart {n : Type*} (W : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (W + W.transpose)

noncomputable def antisymmetricPart {n : Type*} (W : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (W - W.transpose)

theorem symmetricPart_transpose {n : Type*} (W : Matrix n n ℝ) :
    (symmetricPart W).transpose = symmetricPart W := by
  ext i j
  simp [symmetricPart, Matrix.transpose_apply]
  ring

theorem antisymmetricPart_transpose {n : Type*} (W : Matrix n n ℝ) :
    (antisymmetricPart W).transpose = -antisymmetricPart W := by
  ext i j
  simp [antisymmetricPart, Matrix.transpose_apply]
  ring

theorem symmetricPart_add_antisymmetricPart {n : Type*} (W : Matrix n n ℝ) :
    symmetricPart W + antisymmetricPart W = W := by
  ext i j
  simp [symmetricPart, antisymmetricPart, Matrix.transpose_apply]
  ring

theorem symmetricPart_eq_of_symmetric_add_skew
    {n : Type*} {W S A : Matrix n n ℝ}
    (hS : S.transpose = S)
    (hA : A.transpose = -A)
    (decomposition : S + A = W) :
    symmetricPart W = S := by
  ext i j
  have hSij := congrArg (fun M : Matrix n n ℝ => M i j) hS
  have hAij := congrArg (fun M : Matrix n n ℝ => M i j) hA
  have hWij := congrArg (fun M : Matrix n n ℝ => M i j) decomposition
  have hWji := congrArg (fun M : Matrix n n ℝ => M j i) decomposition
  simp [symmetricPart, Matrix.transpose_apply] at hSij hAij hWij hWji ⊢
  linarith

theorem antisymmetricPart_eq_of_symmetric_add_skew
    {n : Type*} {W S A : Matrix n n ℝ}
    (hS : S.transpose = S)
    (hA : A.transpose = -A)
    (decomposition : S + A = W) :
    antisymmetricPart W = A := by
  ext i j
  have hSij := congrArg (fun M : Matrix n n ℝ => M i j) hS
  have hAij := congrArg (fun M : Matrix n n ℝ => M i j) hA
  have hWij := congrArg (fun M : Matrix n n ℝ => M i j) decomposition
  have hWji := congrArg (fun M : Matrix n n ℝ => M j i) decomposition
  simp [antisymmetricPart, Matrix.transpose_apply] at hSij hAij hWij hWji ⊢
  linarith

end InfoGeometry.Physics
