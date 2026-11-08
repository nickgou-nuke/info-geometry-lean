/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FrechetPeirceStabilizer
import InfoGeometry.Examples.RealMatrixModeWitness

/-! # A nonzero Peirce stabilization defect in the tensor tower

The existing dense, nondiagonal square-zero matrix witnesses a nonzero
continuous inner derivation of the cut. Faithful stage maps and the actual
colimit inclusion preserve that defect.
-/

noncomputable section

namespace InfoGeometry.Canonical.FrechetPeirceStabilizerWitness

open scoped Matrix Matrix.Norms.Operator
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Canonical.RealStarColimitUniversal
open InfoGeometry.Canonical.TensorStageFrechetConnection
open InfoGeometry.Canonical.TensorFrechetPeirceGrading
open InfoGeometry.Canonical.FrechetPeirceStabilizer
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Examples.RealMatrixModeWitness

/-- The existing dense square-zero mode acts nontrivially on the cut. -/
theorem denseMode_derivation_cut : stageInnerFrechet 2 x p = -x := by
  change x * p - p * x = -x
  rw [x_mul_p, p_mul_x, zero_sub]

theorem denseMode_ne_zero : x ≠ 0 := by
  intro h
  exact x_entry_ne_zero (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0)
    (congrArg (fun M : Stage 2 => M (((0 : Fin 1), 0), 0) (((0 : Fin 1), 0), 0)) h)

/-- The exact failure of grade compatibility at the dense idempotent is
nonzero; the witness is an actual nondiagnonal matrix derivation. -/
theorem denseMode_peirce_defect_ne_zero :
    stageInnerFrechet 2 x (evenGrade p p) - evenGrade p (stageInnerFrechet 2 x p) ≠ 0 := by
  rw [derivation_evenGrade_defect_at_idempotent _ p p_isIdempotentElem,
    denseMode_derivation_cut]
  exact neg_ne_zero.mpr denseMode_ne_zero

/-- The nonzero defect remains nonzero at every subsequent matrix stage. -/
theorem denseMode_tail_peirce_defect_ne_zero (m : ℕ) (h : 2 ≤ m) :
    let P := bondMap stageBond 2 m h p
    let H := bondMap stageBond 2 m h x
    stageInnerFrechet m H (evenGrade P P) - evenGrade P (stageInnerFrechet m H P) ≠ 0 := by
  dsimp only
  rw [← bondMap_evenGrade, ← bondMap_stageInnerFrechet,
    ← bondMap_stageInnerFrechet, ← bondMap_evenGrade, ← map_sub]
  intro hz
  apply denseMode_peirce_defect_ne_zero
  apply bondMap_injective stageBond (fun k => matStageEmbed_injective k) 2 m h
  simpa only [map_zero] using hz

/-- The same exact nonzero finite-stage defect survives in the faithful
algebraic tensor colimit. -/
theorem denseMode_limit_peirce_defect_ne_zero :
    ofStage 2 (stageInnerFrechet 2 x (evenGrade p p) -
      evenGrade p (stageInnerFrechet 2 x p)) ≠ 0 := by
  intro hz
  exact denseMode_peirce_defect_ne_zero ((ofStage_eq_zero_iff 2 _).mp hz)

/-- The nonzero defect is an explicit difference of actual colimit
operations, rather than only an abstract image of a finite-stage statement. -/
theorem denseMode_limit_intrinsic_peirce_defect_ne_zero :
    (ofStage 2 x * evenGrade (ofStage 2 p) (ofStage 2 p) -
      evenGrade (ofStage 2 p) (ofStage 2 p) * ofStage 2 x) -
      evenGrade (ofStage 2 p)
        (ofStage 2 x * ofStage 2 p - ofStage 2 p * ofStage 2 x) ≠ 0 := by
  simpa only [map_sub, ofStage_evenGrade, ofStage_stageInnerFrechet] using
    denseMode_limit_peirce_defect_ne_zero

end InfoGeometry.Canonical.FrechetPeirceStabilizerWitness

end
