import InfoGeometry.Canonical.BostConnesKTheory
import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Algebra.Grothendieck

/-!
# Bost--Connes KMS Integration on K₀

This file defines the formal evaluation of the Bost--Connes KMS state on the
additive Grothendieck classes of the range projections $S_n S_n^*$.
-/

namespace BostConnesKTheoryIntegration

open InfoGeometry.Arithmetic.BostConnesSystem
open BostConnesKMS
open BostConnesKTheory

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : BostConnesCuntzSystem Op)

/--
The formal evaluation of an additive KMS state on the Grothendieck class.
We lift an assumed additive projection state `φ_add` to `Grothendieck Op →+ ℝ`.
-/
def kmsK0Integration (φ_add : Op →+ ℝ) : Grothendieck Op →+ ℝ :=
  grothendieckLift φ_add

/-- The integration correctly reads out the KMS Boltzmann weight on the range projectors. -/
theorem kmsK0Integration_eval_projector
    (Φ : KMSProjectionState C)
    (φ_add : Op →+ ℝ) (h_eq : ∀ x, φ_add x = Φ.φ x) (n : ℕ+) :
    kmsK0Integration φ_add (projectorGrothendieckClass C n) =
      ((n : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ := by
  dsimp [kmsK0Integration, projectorGrothendieckClass, kmsProjector]
  rw [grothendieckLift_comp]
  rw [h_eq]
  exact Φ.kms_evaluation_on_diagonal_projection n

/--
The integration respects the inclusion--exclusion principle
proved in `projectorGrothendieckClass_inclusion_exclusion`.
-/
theorem kmsK0Integration_inclusion_exclusion
    (φ_add : Op →+ ℝ) (n m : ℕ+) :
    kmsK0Integration φ_add (projectorGrothendieckClass C n) +
    kmsK0Integration φ_add (projectorGrothendieckClass C m) =
      kmsK0Integration φ_add (grothendieckMap Op (kmsProjector C n + kmsProjector C m - kmsProjector C n * kmsProjector C m)) +
      kmsK0Integration φ_add (grothendieckMap Op (kmsProjector C n * kmsProjector C m)) := by
  have h := projectorGrothendieckClass_inclusion_exclusion C n m
  calc
    kmsK0Integration φ_add (projectorGrothendieckClass C n) + kmsK0Integration φ_add (projectorGrothendieckClass C m)
      = kmsK0Integration φ_add (projectorGrothendieckClass C n + projectorGrothendieckClass C m) := by rw [map_add]
    _ = kmsK0Integration φ_add (grothendieckMap Op (kmsProjector C n + kmsProjector C m - kmsProjector C n * kmsProjector C m) + grothendieckMap Op (kmsProjector C n * kmsProjector C m)) := by rw [h]
    _ = kmsK0Integration φ_add (grothendieckMap Op (kmsProjector C n + kmsProjector C m - kmsProjector C n * kmsProjector C m)) + kmsK0Integration φ_add (grothendieckMap Op (kmsProjector C n * kmsProjector C m)) := by rw [map_add]

/--
The explicit physical weights satisfy the inclusion-exclusion sum rule when evaluated
on the Grothendieck classes.
-/
theorem kmsK0Integration_weight_inclusion_exclusion
    (Φ : KMSProjectionState C)
    (φ_add : Op →+ ℝ) (h_eq : ∀ x, φ_add x = Φ.φ x) (n m : ℕ+) :
    (((n : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ) + (((m : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ) =
      kmsK0Integration φ_add (grothendieckMap Op (kmsProjector C n + kmsProjector C m - kmsProjector C n * kmsProjector C m)) +
      kmsK0Integration φ_add (grothendieckMap Op (kmsProjector C n * kmsProjector C m)) := by
  rw [← kmsK0Integration_eval_projector C Φ φ_add h_eq n]
  rw [← kmsK0Integration_eval_projector C Φ φ_add h_eq m]
  exact kmsK0Integration_inclusion_exclusion C φ_add n m

end BostConnesKTheoryIntegration
