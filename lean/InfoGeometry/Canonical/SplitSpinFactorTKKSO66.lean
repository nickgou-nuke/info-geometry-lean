import InfoGeometry.Canonical.SplitSpinFactorTKKConformalSO66
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

end InfoGeometry.Canonical.SplitSpinFactorTKKSO66
