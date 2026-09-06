import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Lie.SplitOctonionStandardDerivationRootBridge
import InfoGeometry.Lie.CanonicalZornStandardDerivationActions
import InfoGeometry.Canonical.SplitOctonionClassificationCore

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.CanonicalZornStandardDerivationActions
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

abbrev Der := CanonicalZornCartanAdjointRootDecomposition.Der

private theorem rootDerivation_10_eq_neg_standard :
    rootDerivation 10 =
      -(canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 0)) := by
  apply canonicalParameterLinearEquiv.symm.injective
  simp only [rootDerivation, LinearEquiv.symm_apply_apply]
  rw [map_neg, standardColumn_E11_U0]
  funext i
  by_cases hi : i = 10 <;>
    simp [CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
      SplitOctonionStandardDerivation.parameterUnit, hi]

private theorem rootDerivation_0_eq_standard :
    rootDerivation 0 =
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 0) := by
  apply canonicalParameterLinearEquiv.symm.injective
  simp only [rootDerivation, LinearEquiv.symm_apply_apply]
  rw [standardColumn_E11_V0]
  funext i
  by_cases hi : i = 0 <;>
    simp [CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
      SplitOctonionStandardDerivation.parameterUnit, hi]

private theorem rootDerivation_eq_smul_standard
    (j : Fin 14)
    (x y : InfoGeometry.Canonical.ZornMatrix ℝ)
    (r : ℝ) (hr : r ≠ 0)
    (h : canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical x y) =
        SplitOctonionStandardDerivation.parameterUnit j r) :
    rootDerivation j = r⁻¹ • canonicalStandardDerivationOfCanonical x y := by
  apply canonicalParameterLinearEquiv.symm.injective
  simp only [rootDerivation, LinearEquiv.symm_apply_apply, map_smul]
  rw [h]
  funext i
  by_cases hi : i = j <;>
    simp [CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
      SplitOctonionStandardDerivation.parameterUnit, hi, hr]

theorem opposite_root_double_bracket_0_10 :
    ⁅⁅rootDerivation 0, rootDerivation 10⁆, rootDerivation 0⁆ ≠ 0 := by
  rw [rootDerivation_0_eq_standard, rootDerivation_10_eq_neg_standard]
  exact InfoGeometry.Lie.CanonicalZornStandardDerivationActions.opposite_standard_double_v_u 0

private theorem rootDerivation_3_eq_standard :
    rootDerivation 3 =
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 1) := by
  simpa using rootDerivation_eq_smul_standard 3 canonicalE11 (canonicalV 1) 1 (by norm_num)
    standardColumn_E11_V1

private theorem rootDerivation_9_eq_standard :
    rootDerivation 9 =
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 1) := by
  simpa using rootDerivation_eq_smul_standard 9 canonicalE11 (canonicalU 1) 1 (by norm_num)
    standardColumn_E11_U1

theorem opposite_root_double_bracket_3_9 :
    ⁅⁅rootDerivation 3, rootDerivation 9⁆, rootDerivation 3⁆ ≠ 0 := by
  rw [rootDerivation_3_eq_standard, rootDerivation_9_eq_standard]
  intro h
  apply InfoGeometry.Lie.CanonicalZornStandardDerivationActions.opposite_standard_double_v_u 1
  have h' := congrArg Neg.neg h
  have h'' :
      -⁅⁅canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 1),
          canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 1)⁆,
        canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 1)⁆ = 0 := by
    simpa only [neg_zero] using h'
  simpa only [lie_neg, neg_lie] using h''

private theorem rootDerivation_4_eq_neg_standard :
    rootDerivation 4 =
      -canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 2) := by
  simpa using rootDerivation_eq_smul_standard 4 canonicalE11 (canonicalU 2) (-1) (by norm_num)
    standardColumn_E11_U2

private theorem rootDerivation_8_eq_standard :
    rootDerivation 8 =
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 2) := by
  simpa using rootDerivation_eq_smul_standard 8 canonicalE11 (canonicalV 2) 1 (by norm_num)
    standardColumn_E11_V2

theorem opposite_root_double_bracket_4_8 :
    ⁅⁅rootDerivation 4, rootDerivation 8⁆, rootDerivation 4⁆ ≠ 0 := by
  rw [rootDerivation_4_eq_neg_standard, rootDerivation_8_eq_standard]
  exact opposite_standard_double_u_v 2

private theorem rootDerivation_1_eq_neg_third_standard :
    rootDerivation 1 =
      (-3 : ℝ)⁻¹ •
        canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0) := by
  exact rootDerivation_eq_smul_standard 1 (canonicalU 1) (canonicalV 0) (-3) (by norm_num)
    standardColumn_U1_V0

private theorem rootDerivation_5_eq_neg_third_standard :
    rootDerivation 5 =
      (-3 : ℝ)⁻¹ •
        canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 1) := by
  exact rootDerivation_eq_smul_standard 5 (canonicalU 0) (canonicalV 1) (-3) (by norm_num)
    standardColumn_U0_V1

private theorem triple_smul_lie
    (c : ℝ) (a b : Der) :
    ⁅⁅c • a, c • b⁆, c • a⁆ = c ^ 3 • ⁅⁅a, b⁆, a⁆ := by
  simp only [smul_lie, lie_smul, smul_smul]
  congr 1
  ring

theorem opposite_root_double_bracket_1_5 :
    ⁅⁅rootDerivation 1, rootDerivation 5⁆, rootDerivation 1⁆ ≠ 0 := by
  rw [rootDerivation_1_eq_neg_third_standard,
    rootDerivation_5_eq_neg_third_standard]
  rw [triple_smul_lie]
  apply smul_ne_zero
  · norm_num
  · have hstd :
        ⁅⁅canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0),
          canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 1)⁆,
          canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0)⁆ ≠
          (0 : Der) :=
      InfoGeometry.Lie.CanonicalZornStandardDerivationActions.opposite_standard_double_cross_1_5
    exact hstd

private theorem rootDerivation_2_eq_neg_third_standard :
    rootDerivation 2 =
      (-3 : ℝ)⁻¹ •
        canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0) := by
  exact rootDerivation_eq_smul_standard 2 (canonicalU 2) (canonicalV 0) (-3) (by norm_num)
    standardColumn_U2_V0

private theorem rootDerivation_11_eq_neg_third_standard :
    rootDerivation 11 =
      (-3 : ℝ)⁻¹ •
        canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 2) := by
  exact rootDerivation_eq_smul_standard 11 (canonicalU 0) (canonicalV 2) (-3) (by norm_num)
    standardColumn_U0_V2

theorem opposite_root_double_bracket_2_11 :
    ⁅⁅rootDerivation 2, rootDerivation 11⁆, rootDerivation 2⁆ ≠ 0 := by
  rw [rootDerivation_2_eq_neg_third_standard,
    rootDerivation_11_eq_neg_third_standard]
  rw [triple_smul_lie]
  apply smul_ne_zero
  · norm_num
  · exact opposite_standard_double_cross_2_11

private theorem rootDerivation_7_eq_neg_third_standard :
    rootDerivation 7 =
      (-3 : ℝ)⁻¹ •
        canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1) := by
  exact rootDerivation_eq_smul_standard 7 (canonicalU 2) (canonicalV 1) (-3) (by norm_num)
    standardColumn_U2_V1

private theorem rootDerivation_12_eq_neg_third_standard :
    rootDerivation 12 =
      (-3 : ℝ)⁻¹ •
        canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 2) := by
  exact rootDerivation_eq_smul_standard 12 (canonicalU 1) (canonicalV 2) (-3) (by norm_num)
    standardColumn_U1_V2

theorem opposite_root_double_bracket_7_12 :
    ⁅⁅rootDerivation 7, rootDerivation 12⁆, rootDerivation 7⁆ ≠ 0 := by
  rw [rootDerivation_7_eq_neg_third_standard,
    rootDerivation_12_eq_neg_third_standard]
  rw [triple_smul_lie]
  apply smul_ne_zero
  · norm_num
  · exact opposite_standard_double_cross_7_12

end InfoGeometry.Lie.CanonicalZornOppositeRootNondegeneracy
