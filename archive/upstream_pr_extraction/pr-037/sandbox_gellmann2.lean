import InfoGeometry.Lie.CanonicalZornG2GellMannRootComparison
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornG2GellMannRootComparison
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.SplitOctonionGellMannCartan
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

noncomputable def gellMannCartan_param (K1 K2 : ℝ) : Params :=
  canonicalParameterLinearEquiv.symm (axialCartanLieEquiv (gellMannCartan K1 K2))

theorem gellMannCartan_param_eq (K1 K2 : ℝ) :
    gellMannCartan_param K1 K2 =
      (K1 - K2) • parameterUnit 6 + (2 * K2) • parameterUnit 13 := by
  apply EquivLike.injective canonicalParameterLinearEquiv
  change canonicalParameterLinearEquiv (canonicalParameterLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  apply LinearMap.ext
  intro X
  have hX : X = canonicalVectorEquiv.symm (canonicalVectorEquiv X) :=
    (Equiv.symm_apply_apply canonicalVectorEquiv X).symm
  nth_rw 1 [hX]
  change _ = canonicalVectorEquiv.symm
    (parameterAction ((K1 - K2) • parameterUnit 6 + (2 * K2) • parameterUnit 13)
      (canonicalVectorEquiv X))
  set Y := canonicalVectorEquiv X
  ext i
  all_goals try fin_cases i
  all_goals simp [parameterUnit,
    axialCartanLieEquiv,
    gellMannCartan, lambda3Traceless, lambda8Traceless,
    lambda3Weights, lambda8Weights,
    axialCartanDerivationIntoLie, axialCartanDerivationLinear,
    axialCartanDerivation, axialCartanEnd,
    parameterAction, canonicalVectorEquiv]
  all_goals try split_ifs
  all_goals try ring
  all_goals try simp
