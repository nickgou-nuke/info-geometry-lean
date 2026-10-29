/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.PeirceLieJordanResolution
import InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution
import InfoGeometry.OperatorAlgebra.LieJordanEndomorphisms
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Lie--Jordan and Peirce actions on the actual matrix-tower direct limit

The target is the existing noncommutative `Cl11TensorTowerLimit.Limit`.
No new colimit carrier is introduced. Naturality identifies the finite
operators with the full algebraic actions on the limit. Injectivity reflects
nonzero coupling defects rather than erasing them. No topological completion
or differentiability assertion follows from these algebraic statements.
-/

noncomputable section

namespace InfoGeometry.Canonical.LieJordanTensorColimit

open InfoGeometry.OperatorAlgebra.LieJordan
open InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- The actual canonical inclusion intertwines the plus action. -/
theorem ofStage_plus (n : ℕ) (H S X : Stage n) :
    ofStage n (plus ℝ H S X) =
      plus ℝ (ofStage n H) (ofStage n S) (ofStage n X) := by
  simp only [plus_apply, map_add, map_sub, map_mul]

theorem ofStage_minus (n : ℕ) (H S X : Stage n) :
    ofStage n (minus ℝ H S X) =
      minus ℝ (ofStage n H) (ofStage n S) (ofStage n X) := by
  simp only [minus_apply, map_add, map_sub, map_mul]

/-- All four existing Peirce corners survive the same canonical inclusion. -/
theorem ofStage_corner (n : ℕ) (P X : Stage n) (i j : Bool) :
    ofStage n (InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution.corner ℝ P i j X) =
      InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution.corner ℝ
        (ofStage n P) i j (ofStage n X) := by
  cases i <;> cases j <;>
    simp [InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution.corner_apply,
      compIdempotent,
      map_mul, map_sub, map_one]

/-- The Peirce frame remains idempotent in the limit. -/
theorem ofStage_idempotent (n : ℕ) {P : Stage n} (hP : IsIdempotent P) :
    IsIdempotent (ofStage n P) := by
  change ofStage n P * ofStage n P = ofStage n P
  rw [← map_mul, show P * P = P from hP]

/-- Independence of the chosen later finite representative for the full operator. -/
theorem plus_representative_independent (m n : ℕ) (hmn : m ≤ n)
    (H S X : Stage m) :
    ofStage n
      (plus ℝ (bondMap stageBond m n hmn H) (bondMap stageBond m n hmn S)
        (bondMap stageBond m n hmn X)) = ofStage m (plus ℝ H S X) := by
  have hmap :
      plus ℝ (bondMap stageBond m n hmn H) (bondMap stageBond m n hmn S)
        (bondMap stageBond m n hmn X) =
      bondMap stageBond m n hmn (plus ℝ H S X) := by
    simp only [plus_apply, map_add, map_sub, map_mul]
  rw [hmap]
  exact directLimitOf_bondMap stageBond m n hmn _

/-- Nonzero matrix defects cannot vanish in this injective tower. -/
theorem ofStage_nonzero (n : ℕ) {X : Stage n} (hX : X ≠ 0) : ofStage n X ≠ 0 := by
  have hinj : Function.Injective (ofStage n) := by
    apply directLimitOf_injective stageBond
    intro k
    change Function.Injective (matStageEmbed k)
    exact matStageEmbed_injective k
  intro h
  apply hX
  apply hinj
  simpa using h

/-- The noncommuting mixed Jordan term is preserved by the actual inclusion. -/
theorem ofStage_mixed_defect (n : ℕ) (H S X : Stage n) :
    ofStage n (jordanOp ℝ (H * S - S * H) X) =
      jordanOp ℝ (ofStage n H * ofStage n S - ofStage n S * ofStage n H)
        (ofStage n X) := by
  simp only [jordanOp_apply, map_add, map_sub, map_mul]

/-- A finite nonzero coupling remains nonzero at the inductive boundary. -/
theorem mixed_defect_survives (n : ℕ) (H S X : Stage n)
    (h : jordanOp ℝ (H * S - S * H) X ≠ 0) :
    jordanOp ℝ (ofStage n H * ofStage n S - ofStage n S * ofStage n H)
      (ofStage n X) ≠ 0 := by
  rw [← ofStage_mixed_defect]
  exact ofStage_nonzero n h

end InfoGeometry.Canonical.LieJordanTensorColimit
