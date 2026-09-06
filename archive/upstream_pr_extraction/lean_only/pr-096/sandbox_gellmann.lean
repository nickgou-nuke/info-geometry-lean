import InfoGeometry.Lie.CanonicalZornG2GellMannRootComparison
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornG2GellMannRootComparison
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.SplitOctonionGellMannCartan
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

theorem test_h2 : gellMannH2_param = - parameterUnit 6 + 2 • parameterUnit 13 := by
  apply EquivLike.injective canonicalParameterLinearEquiv
  change canonicalParameterLinearEquiv (canonicalParameterLinearEquiv.symm gellMannH2) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  have hX : X = canonicalVectorEquiv.symm (canonicalVectorEquiv X) := (Equiv.symm_apply_apply canonicalVectorEquiv X).symm
  nth_rw 1 [hX]
  change _ = canonicalVectorEquiv.symm (parameterAction (- parameterUnit 6 + 2 • parameterUnit 13) (canonicalVectorEquiv X))
  set Y := canonicalVectorEquiv X
  ext i
  all_goals try fin_cases i
  all_goals simp [gellMannH2, parameterUnit,
    axialCartanLieEquiv,
    gellMannCartan, lambda8Traceless, lambda8Weights,
    axialCartanDerivationIntoLie, axialCartanDerivationLinear,
    axialCartanDerivation, axialCartanEnd,
    parameterAction, canonicalVectorEquiv]
  all_goals try split_ifs
  all_goals ring
