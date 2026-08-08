import Mathlib.Algebra.Lie.SkewAdjoint
import proofs.SplitOctonionNorm44

open SplitOctonion
open SplitOctonionNorm44

def splitBilinForm : LinearMap.BilinForm ℝ SplitOct where
  toFun x := {
    toFun := fun y => splitBilinear x y
    map_add' := by intros y1 y2; dsimp [splitBilinear, splitNorm, add_def, sub_def]; ring
    map_smul' := by intros c y; dsimp [splitBilinear, splitNorm, smul_def, sub_def, add_def]; ring
  }
  map_add' := by
    intros x1 x2; ext y
    dsimp [splitBilinear, splitNorm, add_def, sub_def]; ring
  map_smul' := by
    intros c x; ext y
    dsimp [splitBilinear, splitNorm, smul_def, add_def, sub_def]; ring

abbrev SO44 := skewAdjointLieSubalgebra splitBilinForm
