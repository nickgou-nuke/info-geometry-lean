/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorExactCurvatureNonzero
import InfoGeometry.Canonical.TensorStageFrechetConnection

/-!
# Nontrivial Fréchet–Leibniz curvature defect

The existing dense stage-two matrix mode is an explicit vector on which the
CE curvature acts nontrivially. The result also applies to the finite
continuous covariant derivation commutator via the established colimit map.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorFrechetCurvatureWitness

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.TensorStageExactConnection
open InfoGeometry.Canonical.TensorLimitExactConnection
open InfoGeometry.Canonical.TensorExactCurvatureNonzero
open InfoGeometry.Canonical.TensorStageFrechetConnection
open InfoGeometry.Canonical.OperatorFrechetDerivationJet
open InfoGeometry.Canonical.FrechetCECovariantConnection
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.Optics.OperatorDerivationForms
open InfoGeometry.Examples.RealMatrixModeWitness
open InfoGeometry.Canonical.RealStarColimitUniversal
open scoped Matrix Matrix.Norms.Operator

/-- Curvature acts nontrivially on the non-diagonal nilpotent mode. -/
theorem denseMode_curvature_action :
    exactCutCurvature 2 p x (star x) * x - x * exactCutCurvature 2 p x (star x) =
      -(x + x) := by
  have h1 : x * star x * x = x := by rw [x_mul_star_x, p_mul_x]
  have h2 : star x * x * x = 0 := by rw [mul_assoc, x_square_zero, mul_zero]
  have h3 : x * (star x * x) = x := by rw [← mul_assoc, h1]
  have h4 : x * (x * star x) = 0 := by rw [← mul_assoc, x_square_zero, zero_mul]
  rw [denseMode_exactCurvature]
  simp only [neg_mul, mul_neg, sub_mul, mul_sub, h1, h2, h3, h4, sub_zero, zero_sub]
  abel

/-- The vector produced by that curvature action is nonzero. -/
theorem denseMode_twice_ne_zero : -(x + x) ≠ 0 := by
  intro h
  have he := congrArg (fun a : Stage 2 => a (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0)) h
  change -(x (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0) +
    x (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0)) = (0 : ℝ) at he
  norm_num [x] at he

/-- At every tensor refinement, the transported curvature acts nontrivially
on the transported dense nilpotent mode. -/
theorem denseMode_tail_curvature_action_nonzero (m : ℕ) (h : 2 ≤ m) :
    exactCutCurvature m (bondMap stageBond 2 m h p)
        (bondMap stageBond 2 m h x) (bondMap stageBond 2 m h (star x)) *
      bondMap stageBond 2 m h x -
    bondMap stageBond 2 m h x *
      exactCutCurvature m (bondMap stageBond 2 m h p)
        (bondMap stageBond 2 m h x) (bondMap stageBond 2 m h (star x)) ≠ 0 := by
  rw [← bondMap_exactCutCurvature h p x (star x),
    ← map_mul, ← map_mul, ← map_sub, denseMode_curvature_action]
  intro hz
  apply denseMode_twice_ne_zero
  apply bondMap_injective stageBond (fun k => matStageEmbed_injective k) 2 m h
  simpa only [map_zero] using hz

/-- The continuous covariant Leibniz commutator defect is nonzero at every
stage containing the dense witness. -/
theorem denseMode_tail_frechet_defect_nonzero (m : ℕ) (h : 2 ≤ m) :
    let P := bondMap stageBond 2 m h p
    let X := bondMap stageBond 2 m h x
    let Y := bondMap stageBond 2 m h (star x)
    let Γ := exteriorDerivativeZero (realDerivationsLane (Stage m)) P
    covariantFrechet Γ (stageInnerFrechet m X)
        (covariantFrechet Γ (stageInnerFrechet m Y) X) -
      covariantFrechet Γ (stageInnerFrechet m Y)
        (covariantFrechet Γ (stageInnerFrechet m X) X) -
      covariantFrechet Γ (FrechetOperatorDerivation.commutator
        (stageInnerFrechet m X) (stageInnerFrechet m Y)) X ≠ 0 := by
  dsimp only
  rw [covariantFrechet_curvature, stageInnerFrechet_toRealDerivation,
    stageInnerFrechet_toRealDerivation]
  change exactCutCurvature m (bondMap stageBond 2 m h p)
      (bondMap stageBond 2 m h x) (bondMap stageBond 2 m h (star x)) *
    bondMap stageBond 2 m h x - bondMap stageBond 2 m h x *
      exactCutCurvature m (bondMap stageBond 2 m h p)
        (bondMap stageBond 2 m h x) (bondMap stageBond 2 m h (star x)) ≠ 0
  exact denseMode_tail_curvature_action_nonzero m h

/-- The finite Fréchet commutator defect stays nonzero in the actual colimit. -/
theorem denseMode_frechet_defect_nonzero :
    ofStage 2
      (covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage 2)) p)
          (stageInnerFrechet 2 x)
          (covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage 2)) p)
            (stageInnerFrechet 2 (star x)) x) -
       covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage 2)) p)
          (stageInnerFrechet 2 (star x))
          (covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage 2)) p)
            (stageInnerFrechet 2 x) x) -
       covariantFrechet (exteriorDerivativeZero (realDerivationsLane (Stage 2)) p)
          (FrechetOperatorDerivation.commutator (stageInnerFrechet 2 x)
            (stageInnerFrechet 2 (star x))) x) ≠ 0 := by
  rw [ofStage_frechetCovariant_curvature, ← ofStage_exactCurvature,
    ← map_mul, ← map_mul, ← map_sub, denseMode_curvature_action]
  exact fun h => denseMode_twice_ne_zero ((ofStage_eq_zero_iff 2 _).mp h)

end InfoGeometry.Canonical.TensorFrechetCurvatureWitness

end
