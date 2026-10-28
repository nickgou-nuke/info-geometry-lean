/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.LieJordanBoundaryColimit
import InfoGeometry.Algebra.PeirceSandwichDuality

/-!
# Peirce sandwich duality at the existing noncommutative inductive colimit

The ambient object, bonding maps, faithful inclusions, and universal lift
are the repository's existing `Cl11TensorTowerLimit` construction. These
results transport algebraic operations, not analytic or projective boundaries.
-/

namespace InfoGeometry.Canonical.LieJordanOctetColimit

open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
open InfoGeometry.Algebra.PeirceSandwichDuality
open InfoGeometry.Canonical.LieJordanBoundaryColimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- Both independently chosen coefficients and their corners are transported. -/
theorem ofStage_peirce_cross (n : ℕ) (p a b x : Stage n) :
    ofStage n (crossTransport (R := ℝ) (peirce10 p a) (peirce01 p b) x) =
      crossTransport (R := ℝ)
        (peirce10 (ofStage n p) (ofStage n a))
        (peirce01 (ofStage n p) (ofStage n b)) (ofStage n x) := by
  simp only [crossTransport_apply, peirce10, peirce01, compIdempotent,
    map_add, map_mul, map_sub, map_one]

theorem ofStage_peirce_oriented (n : ℕ) (p a b x : Stage n) :
    ofStage n (orientedTransport (R := ℝ) (peirce10 p a) (peirce01 p b) x) =
      orientedTransport (R := ℝ)
        (peirce10 (ofStage n p) (ofStage n a))
        (peirce01 (ofStage n p) (ofStage n b)) (ofStage n x) := by
  simp only [orientedTransport_apply, peirce10, peirce01, compIdempotent,
    map_mul, map_sub, map_one]

/-- The grading law is proved on the actual limit algebra. -/
theorem reflection_cross_at_limit (n : ℕ) (p a b x : Stage n)
    (hp : p * p = p) :
    (ofStage n p - compIdempotent (ofStage n p)) *
        crossTransport (R := ℝ)
          (peirce10 (ofStage n p) (ofStage n a))
          (peirce01 (ofStage n p) (ofStage n b)) (ofStage n x) =
      orientedTransport (R := ℝ)
        (peirce10 (ofStage n p) (ofStage n a))
        (peirce01 (ofStage n p) (ofStage n b)) (ofStage n x) := by
  have hp' : ofStage n p * ofStage n p = ofStage n p := by
    rw [← map_mul, hp]
  exact reflection_cross_left hp' (ofStage n a) (ofStage n b) (ofStage n x)

theorem cross_bonding_compatible (n : ℕ) (u v x : Stage n) :
    ofStage (n + 1)
        (crossTransport (R := ℝ) (stageEmbed n u) (stageEmbed n v) (stageEmbed n x)) =
      ofStage n (crossTransport (R := ℝ) u v x) := by
  calc
    _ = ofStage (n + 1) (stageEmbed n (crossTransport (R := ℝ) u v x)) := by
      exact congrArg (ofStage (n + 1))
        (map_crossTransport (R := ℝ) (stageEmbed n).toRingHom u v x).symm
    _ = _ := ofStage_apply_bond n _

theorem oriented_bonding_compatible (n : ℕ) (u v x : Stage n) :
    ofStage (n + 1)
        (orientedTransport (R := ℝ) (stageEmbed n u) (stageEmbed n v) (stageEmbed n x)) =
      ofStage n (orientedTransport (R := ℝ) u v x) := by
  calc
    _ = ofStage (n + 1) (stageEmbed n (orientedTransport (R := ℝ) u v x)) := by
      exact congrArg (ofStage (n + 1))
        (map_orientedTransport (R := ℝ) (stageEmbed n).toRingHom u v x).symm
    _ = _ := ofStage_apply_bond n _

theorem lift_cross {B : Type} [Semiring B]
    (f : ∀ n : ℕ, Stage n →+* B) (hf : CompatibleCone stageBond f)
    (n : ℕ) (u v x : Stage n) :
    directLimitLift stageBond f hf
      (crossTransport (R := ℝ) (ofStage n u) (ofStage n v) (ofStage n x)) =
        f n (crossTransport (R := ℝ) u v x) := by
  rw [← ofStage_crossTransport]
  exact directLimitLift_of stageBond f hf n _

theorem lift_oriented {B : Type} [Semiring B]
    (f : ∀ n : ℕ, Stage n →+* B) (hf : CompatibleCone stageBond f)
    (n : ℕ) (u v x : Stage n) :
    directLimitLift stageBond f hf
      (orientedTransport (R := ℝ) (ofStage n u) (ofStage n v) (ofStage n x)) =
        f n (orientedTransport (R := ℝ) u v x) := by
  rw [← ofStage_orientedTransport]
  exact directLimitLift_of stageBond f hf n _

end InfoGeometry.Canonical.LieJordanOctetColimit
