/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SymmetricDissipator
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-! # Faithful dissipator transport through the real matrix tensor tower

The carrier is the existing noncommutative algebraic direct limit of the full
real matrix stages. All coefficients are transported, with their order intact.
This proves algebraic transport and reflection, not a spectral gap or completion.
-/

namespace InfoGeometry.Canonical.SymmetricDissipatorColimit

open InfoGeometry.OperatorAlgebra.SymmetricDissipator
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

theorem ofStage_dissipator (n : ℕ) (u v x : Stage n) :
    ofStage n (Core.SquareZeroSandwich.symmDissipator u v x) =
      dissipator (R := ℝ) (ofStage n u) (ofStage n v) (ofStage n x) := by
  rw [← matrix_dissipator]
  exact map_dissipator (ofStage n) u v x

/-- Both coefficients and the input are refined along the actual tower bond. -/
theorem dissipator_bonding_compatible (n : ℕ) (u v x : Stage n) :
    ofStage (n + 1)
        (dissipator (R := ℝ) (stageEmbed n u) (stageEmbed n v) (stageEmbed n x)) =
      ofStage n (dissipator (R := ℝ) u v x) := by
  have h := map_dissipator (R := ℝ) (stageEmbed n).toRingHom u v x
  change stageEmbed n (dissipator (R := ℝ) u v x) =
    dissipator (R := ℝ) (stageEmbed n u) (stageEmbed n v) (stageEmbed n x) at h
  rw [← h, ofStage_apply_bond]

/-- Faithfulness reflects vanishing as well as preserving it. -/
theorem dissipator_eq_zero_iff (n : ℕ) (u v x : Stage n) :
    dissipator (R := ℝ) (ofStage n u) (ofStage n v) (ofStage n x) = 0 ↔
      Core.SquareZeroSandwich.symmDissipator u v x = 0 := by
  have hi : Function.Injective (ofStage n) := by
    apply directLimitOf_injective stageBond
    intro k
    exact matStageEmbed_injective k
  rw [← ofStage_dissipator, ← map_zero (ofStage n)]
  exact hi.eq_iff

/-- The same faithful statement holds after any finite number of applications. -/
theorem dissipator_iterate_eq_zero_iff (n k : ℕ) (u v x : Stage n) :
    (dissipator (R := ℝ) (ofStage n u) (ofStage n v))^[k] (ofStage n x) = 0 ↔
      (Core.SquareZeroSandwich.symmDissipator u v)^[k] x = 0 := by
  have hi : Function.Injective (ofStage n) := by
    apply directLimitOf_injective stageBond
    intro j
    exact matStageEmbed_injective j
  rw [← map_dissipator_iterate, matrix_dissipator, ← map_zero (ofStage n)]
  exact hi.eq_iff

/-- Noncommutativity cannot disappear under the canonical inclusion. -/
theorem ofStage_noncommute_iff (n : ℕ) (u v : Stage n) :
    ofStage n u * ofStage n v ≠ ofStage n v * ofStage n u ↔ u * v ≠ v * u := by
  have hi : Function.Injective (ofStage n) := by
    apply directLimitOf_injective stageBond
    intro j
    exact matStageEmbed_injective j
  rw [← map_mul, ← map_mul, hi.ne_iff]

/-- The universal ring map evaluates the transported dissipator at its source. -/
theorem lift_dissipator {B : Type} [Semiring B]
    (f : ∀ n : ℕ, Stage n →+* B) (hf : CompatibleCone stageBond f)
    (n : ℕ) (u v x : Stage n) :
    directLimitLift stageBond f hf
      (dissipator (R := ℝ) (ofStage n u) (ofStage n v) (ofStage n x)) =
        f n (Core.SquareZeroSandwich.symmDissipator u v x) := by
  rw [← ofStage_dissipator]
  exact directLimitLift_of stageBond f hf n _

end InfoGeometry.Canonical.SymmetricDissipatorColimit
