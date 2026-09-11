import InfoGeometry.KK.RealSplitKreinKasparovCycle
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Equivariance interface for the primitive real split-Krein cycle

This owner records the exact algebraic hypotheses needed to call a bounded
real split-Krein cycle equivariant.  It deliberately does not assert an
analytic `KK^G` class, a group integration, or a Kasparov product.  Those are
separate layers.  The present interface only transports a Lie-algebra action
through the bounded phase, grading, and represented algebra actions.
-/

noncomputable section

namespace InfoGeometry.KK.RealSplitKreinEquivarianceBridge

open InfoGeometry.KK
open InfoGeometry.Krein

variable {A B H 𝔤 : Type*}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [KreinSpace H] [KreinGradedModule H]
variable [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

/-- A proof-carrying Lie-algebra action on the primitive bounded cycle.

The fields are intentionally operator-level.  In particular, `action` is a
Lie homomorphism into bounded endomorphisms, while the three commutation
fields are the exact equivariance conditions used below.
-/
structure EquivariantDatum
    (X : RealSplitKreinKasparovCycle A B H) where
  action : 𝔤 →ₗ⁅ℝ⁆ EndH H
  commutes_phase : ∀ D, action D * X.F = X.F * action D
  commutes_grade : ∀ D,
    action D * KreinGradedModule.gradeCLM (H := H) =
      KreinGradedModule.gradeCLM (H := H) * action D
  commutes_left_rep : ∀ D a, action D * X.π a = X.π a * action D
  commutes_right_rep : ∀ D b, action D * X.ρ b = X.ρ b * action D

variable {X : RealSplitKreinKasparovCycle A B H}

theorem action_commutes_phase_commutator
    (E : EquivariantDatum X) (D : 𝔤) (a : A) :
    E.action D * (X.F * X.π a - X.π a * X.F) =
      (X.F * X.π a - X.π a * X.F) * E.action D := by
  calc
    E.action D * (X.F * X.π a - X.π a * X.F) =
        (E.action D * X.F) * X.π a -
          (E.action D * X.π a) * X.F := by
            simp only [mul_sub, mul_assoc]
    _ = (X.F * E.action D) * X.π a -
          (X.π a * E.action D) * X.F := by
            rw [E.commutes_phase D, E.commutes_left_rep D a]
    _ = X.F * (E.action D * X.π a) -
          X.π a * (E.action D * X.F) := by
            simp only [mul_assoc]
    _ = X.F * (X.π a * E.action D) -
          X.π a * (X.F * E.action D) := by
            rw [E.commutes_left_rep D a, E.commutes_phase D]
    _ = (X.F * X.π a - X.π a * X.F) * E.action D := by
            simp only [sub_mul, mul_assoc]

theorem action_commutes_phase_square_defect
    (E : EquivariantDatum X) (D : 𝔤) :
    E.action D * (X.F * X.F - (1 : EndH H)) =
      (X.F * X.F - (1 : EndH H)) * E.action D := by
  calc
    E.action D * (X.F * X.F - (1 : EndH H)) =
        (E.action D * X.F) * X.F - E.action D := by
          simp only [mul_sub, mul_one, mul_assoc]
    _ = (X.F * E.action D) * X.F - E.action D := by
          rw [E.commutes_phase D]
    _ = X.F * (E.action D * X.F) - E.action D := by
          simp only [mul_assoc]
    _ = X.F * (X.F * E.action D) - E.action D := by
          rw [E.commutes_phase D]
    _ = (X.F * X.F - (1 : EndH H)) * E.action D := by
          simp only [sub_mul, one_mul, mul_assoc]

theorem action_preserves_compact_phase_defects
    (E : EquivariantDatum X) (D : 𝔤) (a : A) :
    E.action D * (X.F * X.F - (1 : EndH H)) =
        (X.F * X.F - (1 : EndH H)) * E.action D ∧
      E.action D * (X.F * X.π a - X.π a * X.F) =
        (X.F * X.π a - X.π a * X.F) * E.action D := by
  exact ⟨action_commutes_phase_square_defect E D,
    action_commutes_phase_commutator E D a⟩

theorem action_commutes_right_rep
    (E : EquivariantDatum X) (D : 𝔤) (b : B) :
    E.action D * X.ρ b = X.ρ b * E.action D :=
  E.commutes_right_rep D b

theorem action_preserves_phase_and_representations
    (E : EquivariantDatum X) (D : 𝔤) :
    E.action D * X.F = X.F * E.action D ∧
      (∀ a : A, E.action D * X.π a = X.π a * E.action D) ∧
      (∀ b : B, E.action D * X.ρ b = X.ρ b * E.action D) := by
  exact ⟨E.commutes_phase D, E.commutes_left_rep D, E.commutes_right_rep D⟩

theorem action_preserves_grading
    (E : EquivariantDatum X) (D : 𝔤) :
    E.action D * KreinGradedModule.gradeCLM (H := H) =
      KreinGradedModule.gradeCLM (H := H) * E.action D :=
  E.commutes_grade D

end InfoGeometry.KK.RealSplitKreinEquivarianceBridge
