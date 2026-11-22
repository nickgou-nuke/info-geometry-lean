/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitSpinFactorTKKLinearParameterization
import InfoGeometry.Canonical.SplitSpinFactorTKKInjectivityNative

noncomputable section

/-! Compatibility path for the upstream SO(6,6) TKK owner.  The executable
construction is owned by `SplitSpinFactorTKKConformalSO66`. -/
namespace InfoGeometry.Canonical.SplitSpinFactorTKKSO66

open InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66

abbrev V10 := SplitSpinFactorTKKConformalSO66.V10
abbrev Carrier12 := SplitSpinFactorTKKConformalSO66.V12
abbrev End12 := Module.End ℝ Carrier12
noncomputable abbrev B10 := SplitSpinFactorTKKConformalSO66.B10
noncomputable abbrev B66 := SplitSpinFactorTKKConformalSO66.B66
noncomputable abbrev translation := SplitSpinFactorTKKConformalSO66.pGen
noncomputable abbrev specialConformal := SplitSpinFactorTKKConformalSO66.kGen
noncomputable abbrev dilation := SplitSpinFactorTKKConformalSO66.dGen
noncomputable abbrev middleRotation := SplitSpinFactorTKKConformalSO66.rotGen

theorem tkk_dimension_packet : Module.finrank ℝ V10 = 10 :=
  SplitSpinFactorTKKConformalSO66.V10_finrank

theorem so66_expected_dimension : 12 * 11 / 2 = 66 := by norm_num


abbrev B10_symm := SplitSpinFactorTKKConformalSO66.B10_symm
abbrev B10_self := SplitSpinFactorTKKConformalSO66.B10_self
abbrev B10_add_left := SplitSpinFactorTKKConformalSO66.B10_add_left
abbrev B10_add_right := SplitSpinFactorTKKInjectivityNative.B10_add_right
abbrev B10_smul_left := SplitSpinFactorTKKConformalSO66.B10_smul_left
abbrev B10_smul_right := SplitSpinFactorTKKConformalSO66.B10_smul_right
abbrev B66_symm := SplitSpinFactorTKKConformalSO66.B66_symm


/-- Infinitesimal orthogonality for a linear endomorphism. -/
def IsB66Skew (A : End12) : Prop := ∀ x y, B66 (A x) y + B66 x (A y) = 0

def commutator (A B : V12 → V12) : V12 → V12 := fun x => A (B x) - B (A x)

def rankTwoRotation (u v : V10) : Module.End ℝ V10 where
  toFun z := B10 u z • v - B10 v z • u
  map_add' x y := by
    simp [B10_add_right, add_smul, sub_eq_add_neg]
    module
  map_smul' r x := by
    simp [B10_smul_right, smul_smul, sub_eq_add_neg]

end InfoGeometry.Canonical.SplitSpinFactorTKKSO66
