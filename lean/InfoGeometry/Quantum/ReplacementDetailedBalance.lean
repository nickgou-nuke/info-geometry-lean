/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.ReplacementHamiltonian
import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

/-!
# Detailed balance for the finite replacement dissipator

The existing replacement channel has observable dual `A ↦ trace (σ * A) • 1`.
We construct that map from the existing complex-linear `weightedTrace` and
prove trace duality, right-weight intertwining, and symmetry for the explicit
pairing `trace (σ * (star A * B))` on the full matrix algebra.

For a positive trace-one target and a nonnegative real rate, the Dirichlet
form is the rate times centered covariance and is nonnegative. Positivity
follows from matrix conjugation and trace positivity. Observables need not
commute with the target. No new inner-product instance, entropy-gradient
representation, or identification with the separately owned BKM pairing is
introduced.
-/

noncomputable section

namespace InfoGeometry.Quantum.ReplacementDetailedBalance

open Matrix
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open InfoGeometry.Quantum.ReplacementStateChannel
open InfoGeometry.Quantum.ReplacementHamiltonian
open InfoGeometry.OperatorAlgebra.LieJordanDuality
open scoped ComplexOrder

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- The observable dual, built from the already owned weighted functional. -/
def observableReplacement (σ : Mat) : Module.End ℂ Mat :=
  (weightedTrace σ).smulRight (1 : Mat)

@[simp] theorem observableReplacement_apply (σ A : Mat) :
    observableReplacement σ A = weightedTrace σ A • (1 : Mat) := rfl

/-- The density-weighted sesquilinear pairing, without choosing a norm. -/
def weightedPairing (σ A B : Mat) : ℂ :=
  weightedTrace σ (star A * B)

/-- Hermitian weights make their weighted functional star preserving. -/
theorem weightedTrace_star (σ A : Mat) (hσ : σ.IsHermitian) :
    weightedTrace σ (star A) = star (weightedTrace σ A) := by
  have hstar : star σ = σ := hσ
  change Matrix.trace (σ * star A) = star (Matrix.trace (σ * A))
  calc
    Matrix.trace (σ * star A) = Matrix.trace (star A * σ) :=
      Matrix.trace_mul_comm σ (star A)
    _ = Matrix.trace (star (σ * A)) := by rw [StarMul.star_mul, hstar]
    _ = star (Matrix.trace (σ * A)) := Matrix.trace_conjTranspose (σ * A)

/-- Algebraic trace duality needs neither positivity nor normalization. -/
theorem trace_replacement_dual (σ X A : Mat) :
    Matrix.trace (replacement σ X * A) =
      Matrix.trace (X * observableReplacement σ A) := by
  change Matrix.trace ((Matrix.trace X • σ) * A) =
    Matrix.trace (X * (weightedTrace σ A • (1 : Mat)))
  simp only [Matrix.smul_mul, Matrix.mul_smul, mul_one, Matrix.trace_smul,
    weightedTrace_apply, smul_eq_mul]
  exact mul_comm _ _

/-- Hermitian targets make the state replacement map star preserving. -/
theorem star_replacement (σ X : Mat) (hσ : σ.IsHermitian) :
    star (replacement σ X) = replacement σ (star X) := by
  have hstar : star σ = σ := hσ
  change star (Matrix.trace X • σ) = Matrix.trace (star X) • σ
  rw [star_smul, hstar]
  congr 1
  exact (Matrix.trace_conjTranspose X).symm

/-- The same observable map is the Hilbert--Schmidt adjoint for a Hermitian
target; this is an identity of the actual star-trace pairings. -/
theorem trace_replacement_hilbertSchmidt_adjoint (σ X A : Mat)
    (hσ : σ.IsHermitian) :
    Matrix.trace (star (replacement σ X) * A) =
      Matrix.trace (star X * observableReplacement σ A) := by
  rw [star_replacement σ X hσ]
  exact trace_replacement_dual σ (star X) A

/-- A trace-one target makes the observable map unital. -/
theorem observableReplacement_one (σ : Mat) (hσ : Matrix.trace σ = 1) :
    observableReplacement σ 1 = 1 := by
  change weightedTrace σ (1 : Mat) • (1 : Mat) = 1
  rw [weightedTrace_apply, mul_one, hσ, one_smul]

/-- The normalized weighted functional is stationary under its projection. -/
theorem weightedTrace_observableReplacement (σ A : Mat)
    (hσ : Matrix.trace σ = 1) :
    weightedTrace σ (observableReplacement σ A) = weightedTrace σ A := by
  have hone : weightedTrace σ (1 : Mat) = 1 := by
    simpa only [weightedTrace_apply, mul_one] using hσ
  change weightedTrace σ (weightedTrace σ A • (1 : Mat)) = weightedTrace σ A
  rw [map_smul, hone, smul_eq_mul, mul_one]

/-- The observable map is a projection on the full matrix algebra. -/
theorem observableReplacement_idempotent (σ : Mat)
    (hσ : Matrix.trace σ = 1) :
    (observableReplacement σ).comp (observableReplacement σ) =
      observableReplacement σ := by
  apply LinearMap.ext
  intro A
  change weightedTrace σ (observableReplacement σ A) • (1 : Mat) =
    weightedTrace σ A • (1 : Mat)
  rw [weightedTrace_observableReplacement σ A hσ]

/-- Right multiplication by the target intertwines the two replacement
maps, retaining the matrix-product order. -/
theorem replacement_right_weight (σ A : Mat) :
    replacement σ (A * σ) = observableReplacement σ A * σ := by
  change Matrix.trace (A * σ) • σ = (weightedTrace σ A • (1 : Mat)) * σ
  rw [Matrix.smul_mul, one_mul, weightedTrace_apply, Matrix.trace_mul_comm A σ]

/-- The right projection evaluates to the product of the two expectations. -/
theorem weightedPairing_observableReplacement_right (σ A B : Mat)
    (hσ : σ.IsHermitian) :
    weightedPairing σ A (observableReplacement σ B) =
      star (weightedTrace σ A) * weightedTrace σ B := by
  change weightedTrace σ (star A * (weightedTrace σ B • (1 : Mat))) = _
  rw [Matrix.mul_smul, mul_one, map_smul, weightedTrace_star σ A hσ]
  change weightedTrace σ B * star (weightedTrace σ A) = _
  exact mul_comm _ _

/-- The left projection has the same expectation product. -/
theorem weightedPairing_observableReplacement_left (σ A B : Mat) :
    weightedPairing σ (observableReplacement σ A) B =
      star (weightedTrace σ A) * weightedTrace σ B := by
  change weightedTrace σ (star (weightedTrace σ A • (1 : Mat)) * B) = _
  simp only [star_smul, star_one, Matrix.smul_mul, one_mul, map_smul, smul_eq_mul]

/-- The observable replacement is symmetric for the density-weighted pairing. -/
theorem observableReplacement_weighted_symm (σ A B : Mat)
    (hσ : σ.IsHermitian) :
    weightedPairing σ A (observableReplacement σ B) =
      weightedPairing σ (observableReplacement σ A) B := by
  rw [weightedPairing_observableReplacement_right σ A B hσ,
    weightedPairing_observableReplacement_left]

/-- Matrix conjugation proves weighted positivity, also for singular targets
and the empty matrix index type. -/
theorem weightedPairing_self_nonneg (σ A : Mat) (hσ : σ.PosSemidef) :
    0 ≤ (weightedPairing σ A A).re := by
  have heq : weightedPairing σ A A = Matrix.trace (A * σ * Aᴴ) := by
    change Matrix.trace (σ * (Aᴴ * A)) = Matrix.trace (A * σ * Aᴴ)
    rw [← mul_assoc, Matrix.trace_mul_cycle σ Aᴴ A]
  rw [heq]
  exact (RCLike.nonneg_iff.mp (hσ.mul_mul_conjTranspose_same A).trace_nonneg).1

/-- The real-rate observable generator dual to the existing state dissipator. -/
def observableGenerator (σ : Mat) (γ : ℝ) : Module.End ℂ Mat :=
  γ • (observableReplacement σ - LinearMap.id)

@[simp] theorem observableGenerator_apply (σ A : Mat) (γ : ℝ) :
    observableGenerator σ γ A = γ • (observableReplacement σ A - A) := rfl

/-- Ordered trace duality for the already owned state generator at `K = 0`. -/
theorem trace_generator_dual (σ X A : Mat) (γ : ℝ) :
    Matrix.trace (generator (0 : Mat) σ γ X * A) =
      Matrix.trace (X * observableGenerator σ γ A) := by
  simp only [generator_apply, ad_apply, zero_mul, mul_zero, sub_self, zero_add,
    observableGenerator_apply, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, sub_mul, mul_sub, Matrix.trace_sub]
  rw [trace_replacement_dual]

/-- Hermitian targets promote the trace dual to the star-trace adjoint. -/
theorem trace_generator_hilbertSchmidt_adjoint (σ X A : Mat) (γ : ℝ)
    (hσ : σ.IsHermitian) :
    Matrix.trace (star (generator (0 : Mat) σ γ X) * A) =
      Matrix.trace (star X * observableGenerator σ γ A) := by
  have hstar : star (generator (0 : Mat) σ γ X) =
      generator (0 : Mat) σ γ (star X) := by
    simp only [generator_apply, ad_apply, zero_mul, mul_zero, sub_self, zero_add,
      star_smul, star_trivial, star_sub, star_replacement σ X hσ]
  rw [hstar]
  exact trace_generator_dual σ (star X) A γ

/-- The right-weight detailed-balance identity for the concrete
replacement dissipator. It requires no commutation of `A` and `σ`. -/
theorem generator_right_weight (σ A : Mat) (γ : ℝ) :
    generator (0 : Mat) σ γ (A * σ) = observableGenerator σ γ A * σ := by
  simp only [generator_apply, ad_apply, zero_mul, mul_zero, sub_self, zero_add,
    observableGenerator_apply, Matrix.smul_mul, sub_mul]
  rw [replacement_right_weight]

/-- The observable generator annihilates the unit for a normalized target. -/
theorem observableGenerator_one (σ : Mat) (γ : ℝ)
    (hσ : Matrix.trace σ = 1) : observableGenerator σ γ 1 = 0 := by
  rw [observableGenerator_apply, observableReplacement_one σ hσ, sub_self, smul_zero]

/-- The normalized target functional is stationary under the observable generator. -/
theorem weightedTrace_observableGenerator_zero (σ A : Mat) (γ : ℝ)
    (hσ : Matrix.trace σ = 1) :
    weightedTrace σ (observableGenerator σ γ A) = 0 := by
  change weightedTrace σ (γ • (observableReplacement σ A - A)) = 0
  rw [LinearMap.map_smul_of_tower, map_sub,
    weightedTrace_observableReplacement σ A hσ, sub_self, smul_zero]

/-- Real rates preserve symmetry in the weighted sesquilinear pairing. -/
theorem observableGenerator_weighted_symm (σ A B : Mat) (γ : ℝ)
    (hσ : σ.IsHermitian) :
    weightedPairing σ A (observableGenerator σ γ B) =
      weightedPairing σ (observableGenerator σ γ A) B := by
  change weightedTrace σ (star A * (γ • (observableReplacement σ B - B))) =
    weightedTrace σ (star (γ • (observableReplacement σ A - A)) * B)
  simp only [Matrix.mul_smul, LinearMap.map_smul_of_tower, star_smul,
    star_trivial, Matrix.smul_mul, star_sub, mul_sub, sub_mul, map_sub]
  change γ • (weightedPairing σ A (observableReplacement σ B) - weightedPairing σ A B) =
    γ • (weightedPairing σ (observableReplacement σ A) B - weightedPairing σ A B)
  rw [observableReplacement_weighted_symm σ A B hσ]

/-- Centered covariance for this explicit weighted pairing, distinct from
the interval-integral BKM covariance owned by the canonical Gibbs modules. -/
def weightedCovariance (σ A B : Mat) : ℂ :=
  weightedPairing σ (A - observableReplacement σ A) (B - observableReplacement σ B)

/-- The centered full-matrix covariance is the usual expectation defect. -/
theorem weightedCovariance_eq (σ A B : Mat) (hσ : σ.IsHermitian)
    (htrace : Matrix.trace σ = 1) :
    weightedCovariance σ A B = weightedPairing σ A B -
      star (weightedTrace σ A) * weightedTrace σ B := by
  unfold weightedCovariance weightedPairing
  simp only [star_sub, sub_mul, mul_sub, map_sub]
  change weightedPairing σ A B - weightedPairing σ (observableReplacement σ A) B -
      (weightedPairing σ A (observableReplacement σ B) -
        weightedPairing σ (observableReplacement σ A) (observableReplacement σ B)) = _
  rw [weightedPairing_observableReplacement_right σ A B hσ,
    weightedPairing_observableReplacement_left σ A B,
    weightedPairing_observableReplacement_left σ A (observableReplacement σ B),
    weightedTrace_observableReplacement σ B htrace, sub_self, sub_zero]
  rfl

/-- Positivity of centered covariance follows on the same full matrix carrier. -/
theorem weightedCovariance_self_nonneg (σ A : Mat) (hσ : σ.PosSemidef) :
    0 ≤ (weightedCovariance σ A A).re :=
  weightedPairing_self_nonneg σ (A - observableReplacement σ A) hσ

/-- The negative generator's ordered Dirichlet form is exactly its rate
times centered covariance. This is an identity for arbitrary observables. -/
theorem dirichlet_eq_covariance (σ A B : Mat) (γ : ℝ)
    (hσ : σ.IsHermitian) (htrace : Matrix.trace σ = 1) :
    -weightedPairing σ A (observableGenerator σ γ B) =
      γ • weightedCovariance σ A B := by
  rw [weightedCovariance_eq σ A B hσ htrace]
  change -weightedTrace σ (star A * (γ • (observableReplacement σ B - B))) = _
  rw [Matrix.mul_smul, LinearMap.map_smul_of_tower, mul_sub, map_sub]
  change -(γ • (weightedPairing σ A (observableReplacement σ B) - weightedPairing σ A B)) = _
  rw [weightedPairing_observableReplacement_right σ A B hσ, ← smul_neg, neg_sub]

/-- A nonnegative real relaxation rate has nonnegative Dirichlet form for
every observable and every positive trace-one target. -/
theorem dirichlet_self_nonneg (σ A : Mat) (γ : ℝ)
    (hσ : σ.PosSemidef) (htrace : Matrix.trace σ = 1) (hγ : 0 ≤ γ) :
    0 ≤ (-weightedPairing σ A (observableGenerator σ γ A)).re := by
  rw [dirichlet_eq_covariance σ A A γ hσ.isHermitian htrace]
  rw [Complex.smul_re]
  exact mul_nonneg hγ (weightedCovariance_self_nonneg σ A hσ)

end InfoGeometry.Quantum.ReplacementDetailedBalance

end
