/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.LieJordanBoundaryColimit
import InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge

/-!
# Hodge transport through the existing real tensor-tower colimit

All objects and bonding maps are the existing Cl11TensorTowerLimit owners.
The positive-adjoint assertion is finite-stage; at the algebraic limit we
transport the star-polynomial. The final theorem descends an explicitly
supplied uniform finite inequality and compatible trace, not a fabricated gap.
-/

namespace InfoGeometry.Canonical.LieJordanHodgeColimit

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
open InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble
open InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- The Gram coefficient is preserved by the existing star-compatible inclusion. -/
theorem ofStage_gram (n : ℕ) (u : Stage n) :
    ofStage n (u * star u + star u * u) =
      ofStage n u * star (ofStage n u) + star (ofStage n u) * ofStage n u := by
  simp only [map_add, map_mul, ofStage_star]

theorem ofStage_jordan_gram (n : ℕ) (u x : Stage n) :
    ofStage n (jordanLeft (R := ℝ) (u * star u + star u * u) x) =
      jordanLeft (R := ℝ)
        (ofStage n u * star (ofStage n u) + star (ofStage n u) * ofStage n u)
        (ofStage n x) := by
  change ofStage n ((u * star u + star u * u) * x + x * (u * star u + star u * u)) =
    (ofStage n u * star (ofStage n u) + star (ofStage n u) * ofStage n u) * ofStage n x +
      ofStage n x * (ofStage n u * star (ofStage n u) + star (ofStage n u) * ofStage n u)
  simp only [map_add, map_mul, ofStage_star]

theorem ofStage_coboundary_star (n : ℕ) (u : Stage n) (z : Stage n × Stage n) :
    Prod.map (ofStage n) (ofStage n) (coboundary (R := ℝ) (star u) z) =
      coboundary (R := ℝ) (star (ofStage n u))
        (Prod.map (ofStage n) (ofStage n) z) := by
  simpa only [ofStage_star] using map_coboundary (R := ℝ) (ofStage n) (star u) z

/-- The algebraic Hodge identity holds on the full limit ring, not just images. -/
theorem boundary_coboundary_at_limit (u : Limit) :
    boundary (R := ℝ) u * coboundary (R := ℝ) (star u) +
      coboundary (R := ℝ) (star u) * boundary (R := ℝ) u =
        liftOp (jordanLeft (R := ℝ) (u * star u + star u * u)) :=
  boundary_coboundary u (star u)

theorem gram_bonding_compatible (n : ℕ) (u x : Stage n) :
    ofStage (n + 1)
      (jordanLeft (R := ℝ)
        (stageEmbed n u * star (stageEmbed n u) + star (stageEmbed n u) * stageEmbed n u)
        (stageEmbed n x)) =
      ofStage n (jordanLeft (R := ℝ) (u * star u + star u * u) x) := by
  rw [ofStage_jordan_gram]
  simp only [ofStage_apply_bond]
  exact (ofStage_jordan_gram n u x).symm

/-- The maintained universal map retains the noncommutative ordered readout. -/
theorem lift_jordan_gram {B : Type*} [Semiring B]
    (f : ∀ n : ℕ, Stage n →+* B) (hf : CompatibleCone stageBond f)
    (n : ℕ) (u x : Stage n) :
    directLimitLift stageBond f hf
      (jordanLeft (R := ℝ)
        (ofStage n u * star (ofStage n u) + star (ofStage n u) * ofStage n u)
        (ofStage n x)) =
      f n (jordanLeft (R := ℝ) (u * star u + star u * u) x) := by
  rw [← ofStage_jordan_gram]
  exact directLimitLift_of stageBond f hf n _

/-- Normalized, rather than raw, trace preserves the quadratic energy under bonding. -/
theorem normalized_energy_bond (n : ℕ) (k x : Stage n) :
    normalizedTrace (n + 1)
      (star (stageEmbed n x) *
        (stageEmbed n k * stageEmbed n x + stageEmbed n x * stageEmbed n k)) =
      normalizedTrace n (star x * (k * x + x * k)) := by
  rw [← stageEmbed_star]
  rw [← map_mul, ← map_mul, ← map_add, ← map_mul]
  exact normalizedTrace_matStageEmbed n _

/-- Every limit element has a representative above any prescribed finite stage.
Using a cofinal tail avoids forcing a compatible coefficient to lie in stage 0. -/
theorem exists_stage_above (start : ℕ) (x : Limit) :
    ∃ n, start ≤ n ∧ ∃ y : Stage n, ofStage n y = x := by
  induction x using DirectLimit.induction with
  | _ n y =>
    refine ⟨max start n, le_max_left _ _,
      bondMap stageBond n (max start n) (le_max_right _ _) y, ?_⟩
    exact directLimitOf_bondMap stageBond n (max start n) (le_max_right _ _) y

/-- A uniform finite inequality on a cofinal tail descends to the actual
algebraic colimit. The finite bounds and trace readback remain hypotheses.
Compatibility is NOT imposed at the initial scalar stage. -/
theorem uniform_coercivity_descends
    (start : ℕ) (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ n (x : Stage n), tau (ofStage n x) = normalizedTrace n x)
    (k p : ∀ n, Stage n) (kinf pinf : Limit)
    (hk : ∀ n, start ≤ n → ofStage n (k n) = kinf)
    (hp : ∀ n, start ≤ n → ofStage n (p n) = pinf)
    (gamma : ℝ)
    (hfinite : ∀ n, start ≤ n → ∀ x : Stage n,
      gamma * normalizedTrace n
        (star (x - p n * x * p n) * (x - p n * x * p n)) ≤
      normalizedTrace n (star x * (k n * x + x * k n)))
    (x : Limit) :
    gamma * tau (star (x - pinf * x * pinf) * (x - pinf * x * pinf)) ≤
      tau (star x * (kinf * x + x * kinf)) := by
  obtain ⟨n, hn, y, rfl⟩ := exists_stage_above start x
  rw [← hk n hn, ← hp n hn]
  simpa only [← map_mul, ← map_sub, ← map_add, ← ofStage_star, htau] using hfinite n hn y

end InfoGeometry.Canonical.LieJordanHodgeColimit
