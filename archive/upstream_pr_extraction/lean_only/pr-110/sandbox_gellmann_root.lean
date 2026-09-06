import InfoGeometry.Lie.SplitOctonionGellMannCartan
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Lie.CanonicalZornG2AppendixDSourceBridge
import InfoGeometry.Lie.CanonicalZornDerivationDimension

open InfoGeometry.Lie.SplitOctonionGellMannCartan
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornG2AppendixDSourceBridge
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension

noncomputable section

def gellMannH1 : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  axialCartanLieEquiv (gellMannCartan 1 0)

def gellMannH2 : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  axialCartanLieEquiv (gellMannCartan 0 1)

def gellMannH1_param : Params :=
  canonicalParameterLinearEquiv.symm gellMannH1

def gellMannH2_param : Params :=
  canonicalParameterLinearEquiv.symm gellMannH2

theorem gellMannH1_eq_canonicalCartanCombination :
    gellMannH1_param = parameterUnit 6 := by
  ext i
  fin_cases i <;>
    simp [gellMannH1_param, gellMannH1,
      parameterUnit,
      canonicalParameterLinearEquiv, axialCartanLieEquiv,
      gellMannCartan, lambda3Traceless, lambda3Weights]
  <;> ring

theorem gellMannH2_eq_canonicalCartanCombination :
    gellMannH2_param = parameterUnit 6 + 2 • parameterUnit 13 := by
  ext i
  fin_cases i <;>
    simp [gellMannH2_param, gellMannH2,
      parameterUnit,
      canonicalParameterLinearEquiv, axialCartanLieEquiv,
      gellMannCartan, lambda8Traceless, lambda8Weights]
  <;> ring
