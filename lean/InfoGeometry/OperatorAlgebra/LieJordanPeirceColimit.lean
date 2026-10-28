import InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Lie--Jordan and Peirce transport into the native full-matrix inductive limit

The carrier and bonding maps are owned by `Cl11TensorTowerLimit`. These laws
commute with those actual ring homomorphisms. No topological completion,
state-dependent metric, or analytic continuation is asserted here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LieJordanPeirceColimit

open LieJordanDuality PeirceLieJordanResolution
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower

/-- The native stage inclusion intertwines the positive regular-module action. -/
theorem stage_dualPlus (n : ℕ) (H S X : Stage n) :
    ofStage n (dualPlus ℝ H S X) =
      dualPlus ℝ (ofStage n H) (ofStage n S) (ofStage n X) := by
  simp only [dualPlus_apply, map_add, map_sub, map_mul]

theorem stage_dualMinus (n : ℕ) (H S X : Stage n) :
    ofStage n (dualMinus ℝ H S X) =
      dualMinus ℝ (ofStage n H) (ofStage n S) (ofStage n X) := by
  simp only [dualMinus_apply, map_add, map_sub, map_mul]

/-- All four native Peirce corners commute with the same stage inclusion. -/
theorem stage_corner (n : ℕ) (p X : Stage n) (i j : Bool) :
    ofStage n (corner ℝ p i j X) =
      corner ℝ (ofStage n p) i j (ofStage n X) := by
  cases i <;> cases j <;>
    simp [corner_apply, compIdempotent, map_mul, map_sub]

/-- The full mixed defect is preserved, not discarded at infinity. -/
theorem stage_mixed_defect (n : ℕ) (H S X : Stage n) :
    ofStage n (jordan ℝ (H * S - S * H) X) =
      jordan ℝ (ofStage n H * ofStage n S - ofStage n S * ofStage n H)
        (ofStage n X) := by
  simp only [jordan_apply, map_add, map_sub, map_mul]

/-- Passing through one more matrix stage gives the identical colimit action. -/
theorem stage_dualPlus_bond (n : ℕ) (H S X : Stage n) :
    ofStage (n + 1)
      (dualPlus ℝ (stageEmbed n H) (stageEmbed n S) (stageEmbed n X)) =
      ofStage n (dualPlus ℝ H S X) := by
  rw [← map_dualPlus ℝ (stageEmbed n), ofStage_apply_bond]

theorem stage_dualMinus_bond (n : ℕ) (H S X : Stage n) :
    ofStage (n + 1)
      (dualMinus ℝ (stageEmbed n H) (stageEmbed n S) (stageEmbed n X)) =
      ofStage n (dualMinus ℝ H S X) := by
  rw [← map_dualMinus ℝ (stageEmbed n), ofStage_apply_bond]

/-- The corrected complementary corner identity holds on the actual limit. -/
theorem limit_complementary_corner (n : ℕ) (p : Stage n) (hp : p * p = p)
    (X : Limit) :
    2 • peirce00 (ofStage n p) X =
      2 • X - jordan ℝ (ofStage n p) X +
        ad ℝ (ofStage n p) (ad ℝ (ofStage n p) X) := by
  exact twice_peirce00 ℝ (limit_idempotent hp) X

/-- The four projector compositions hold for arbitrary inputs of the limit,
not only for matrices at the original stage. -/
theorem limit_corner_comp (n : ℕ) (p : Stage n) (hp : p * p = p)
    (i j k l : Bool) :
    corner ℝ (ofStage n p) i j * corner ℝ (ofStage n p) k l =
      if i = k ∧ j = l then corner ℝ (ofStage n p) i j else 0 := by
  exact corner_comp ℝ (limit_idempotent hp) i j k l

end InfoGeometry.OperatorAlgebra.LieJordanPeirceColimit
