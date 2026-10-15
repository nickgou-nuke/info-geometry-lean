import Mathlib.Algebra.Lie.SkewAdjoint
import proofs.SplitOctonionNorm44

open SplitOctonion
open SplitOctonionNorm44

noncomputable def splitBilinForm : LinearMap.BilinForm ℝ SplitOct where
  toFun x := {
    toFun := fun y => splitBilinear x y
    map_add' := by intros y1 y2; dsimp [splitBilinear, splitNorm, add_def, sub_def]; ring
    map_smul' := by intros c y; dsimp [splitBilinear, splitNorm, smul_def, sub_def, add_def]; ring
  }
  map_add' := by
    intros x1 x2
    ext y
    change splitBilinear (x1 + x2) y =
      splitBilinear x1 y + splitBilinear x2 y
    dsimp [splitBilinear, splitNorm, add_def, sub_def]
    ring_nf
  map_smul' := by
    intros c x
    ext y
    change splitBilinear (c • x) y = c * splitBilinear x y
    dsimp [splitBilinear, splitNorm, smul_def, add_def, sub_def]
    ring_nf

noncomputable abbrev SO44 := skewAdjointLieSubalgebra splitBilinForm
