/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.LieJordanBoundaryColimit
import InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Positive-Hodge algebra and quantitative readouts at the existing colimit

The carrier, star, embeddings and universal lift are existing owners.
The quantitative transfer theorem retains its explicit trace-extension,
operator-intertwining and uniform finite-bound hypotheses. It constructs
neither an interacting Hamiltonian nor a spectral completion by definition.
-/

namespace InfoGeometry.Canonical.LieJordanHodgeColimit

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
open InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble
open InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- Native inclusion preserves the exchanged boundary, with both blocks. -/
theorem ofStage_coboundary (n : ℕ) (u : Stage n) (z : Stage n × Stage n) :
    Prod.map (ofStage n) (ofStage n) (coboundary (R := ℝ) u z) =
      coboundary (R := ℝ) (ofStage n u) (Prod.map (ofStage n) (ofStage n) z) := by
  apply Prod.ext
  · change ofStage n (u * z.2 + z.2 * u) = _
    simp only [map_add, map_mul]
    rfl
  · change ofStage n (u * z.1 - z.1 * u) = _
    simp only [map_sub, map_mul]
    rfl

/-- The coefficient uses the existing star, not a silently changed involution. -/
theorem ofStage_hodge_coefficient (n : ℕ) (u : Stage n) :
    ofStage n (u * star u + star u * u) =
      ofStage n u * star (ofStage n u) + star (ofStage n u) * ofStage n u := by
  simp only [map_add, map_mul, ofStage_star]

theorem ofStage_hodge_action (n : ℕ) (u x : Stage n) :
    ofStage n (jordanLeft (R := ℝ) (u * star u + star u * u) x) =
      jordanLeft (R := ℝ)
        (ofStage n u * star (ofStage n u) + star (ofStage n u) * ofStage n u)
        (ofStage n x) := by
  change ofStage n ((u * star u + star u * u) * x +
    x * (u * star u + star u * u)) = _
  simp only [map_add, map_mul, ofStage_star]
  rfl

/-- The exact Jordan identity holds on all of the limit algebra, not only a
commuting sector or a selected finite representative. -/
theorem hodge_identity_at_limit (u : Limit) :
    boundary (R := ℝ) u * coboundary (R := ℝ) (star u) +
      coboundary (R := ℝ) (star u) * boundary (R := ℝ) u =
        liftOp (jordanLeft (R := ℝ) (u * star u + star u * u)) :=
  boundary_coboundary_anticommutator u (star u)

/-- Normalized energy, unlike the unnormalized trace, is unchanged by padding. -/
theorem normalized_energy_bond (n : ℕ) (K x : Stage n) :
    normalizedTrace (n + 1)
      (star (stageEmbed n x) *
        (stageEmbed n K * stageEmbed n x + stageEmbed n x * stageEmbed n K)) =
      normalizedTrace n (star x * (K * x + x * K)) := by
  calc
    _ = normalizedTrace (n + 1) (stageEmbed n (star x * (K * x + x * K))) := by
      congr 1
      simp only [map_mul, map_add, stageEmbed_star]
    _ = _ := normalizedTrace_matStageEmbed n _

/-- Evaluate the positive-pairing readout on an actual finite representative. -/
theorem trace_pair_on_stage (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ n (x : Stage n), tau (ofStage n x) = normalizedTrace n x)
    (n : ℕ) (x y : Stage n) :
    tau (star (ofStage n x) * ofStage n y) = normalizedTrace n (star x * y) := by
  rw [← ofStage_star, ← map_mul, htau]

/-- Positivity is derived from the finite traces for any extending functional. -/
theorem trace_extension_positive (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ n (x : Stage n), tau (ofStage n x) = normalizedTrace n x)
    (x : Limit) : 0 ≤ tau (star x * x) := by
  induction x using DirectLimit.induction with
  | _ n a =>
    change 0 ≤ tau (star (ofStage n a) * ofStage n a)
    rw [trace_pair_on_stage tau htau]
    unfold normalizedTrace
    apply div_nonneg
    · exact (Matrix.posSemidef_conjTranspose_mul_self a).trace_nonneg
    · positivity

/-- Uniform finite-stage coercivity descends by the actual direct-limit
induction principle. No uniform bound is inferred merely from injectivity. -/
theorem uniform_coercivity_at_limit
    (tau : Limit →ₗ[ℝ] ℝ)
    (htau : ∀ n (x : Stage n), tau (ofStage n x) = normalizedTrace n x)
    (H P : Module.End ℝ Limit)
    (Hn Pn : ∀ n, Module.End ℝ (Stage n))
    (hH : ∀ n (x : Stage n), H (ofStage n x) = ofStage n (Hn n x))
    (hP : ∀ n (x : Stage n), P (ofStage n x) = ofStage n (Pn n x))
    (gamma : ℝ)
    (hfinite : ∀ n (x : Stage n),
      gamma * normalizedTrace n (star (x - Pn n x) * (x - Pn n x)) ≤
        normalizedTrace n (star x * Hn n x))
    (x : Limit) :
    gamma * tau (star (x - P x) * (x - P x)) ≤ tau (star x * H x) := by
  induction x using DirectLimit.induction with
  | _ n a =>
    change gamma * tau (star (ofStage n a - P (ofStage n a)) *
      (ofStage n a - P (ofStage n a))) ≤ tau (star (ofStage n a) * H (ofStage n a))
    rw [hP, hH, ← map_sub, trace_pair_on_stage tau htau, trace_pair_on_stage tau htau]
    exact hfinite n a

/-- The universal ring lift evaluates the quadratic Hodge action at the stage. -/
theorem lift_hodge_action {B : Type} [Semiring B]
    (f : ∀ n : ℕ, Stage n →+* B) (hf : CompatibleCone stageBond f)
    (n : ℕ) (u x : Stage n) :
    directLimitLift stageBond f hf
      (jordanLeft (R := ℝ)
        (ofStage n u * star (ofStage n u) + star (ofStage n u) * ofStage n u)
        (ofStage n x)) =
      f n (jordanLeft (R := ℝ) (u * star u + star u * u) x) := by
  rw [← ofStage_hodge_action]
  exact directLimitLift_of stageBond f hf n _

end InfoGeometry.Canonical.LieJordanHodgeColimit
