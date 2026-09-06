import InfoGeometry.Lie.CanonicalZornG2GellMannRootComparison
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

open InfoGeometry.Lie.CanonicalZornG2GellMannRootComparison
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

theorem test_h1 : gellMannH1_param = parameterUnit 6 := by
  apply EquivLike.injective canonicalParameterLinearEquiv
  change canonicalParameterLinearEquiv (canonicalParameterLinearEquiv.symm gellMannH1) = _
  rw [LinearEquiv.apply_symm_apply]
  sorry
