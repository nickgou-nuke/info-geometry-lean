import InfoGeometry.Lie.SplitOctonionStandardDerivation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

namespace InfoGeometry.Lie.SplitOctonionStandardDerivationRootBridge

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

theorem canonicalStandard_eq_smul_rootDerivation
    (x y : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalZorn)
    (j : Fin 14) (r : ℝ)
    (h : canonicalParameterLinearEquiv.symm
      (canonicalStandardDerivationOfCanonical x y) =
      InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit j r) :
    canonicalStandardDerivationOfCanonical x y = r • rootDerivation j := by
  apply canonicalParameterLinearEquiv.symm.injective
  rw [h]
  rw [rootDerivation, map_smul, canonicalParameterLinearEquiv.symm_apply_apply]
  funext i
  by_cases hij : i = j <;>
    simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit, hij]

theorem standardColumn_E11_U0_root :
    canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 0) =
      (-1 : ℝ) • rootDerivation 10 := by
  exact canonicalStandard_eq_smul_rootDerivation _ _ _ _ standardColumn_E11_U0

theorem standardColumn_E11_U1_root :
    canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 1) =
      rootDerivation 9 := by
  simpa using canonicalStandard_eq_smul_rootDerivation _ _ _ _ standardColumn_E11_U1

theorem standardColumn_E11_U2_root :
    canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU 2) =
      (-1 : ℝ) • rootDerivation 4 := by
  exact canonicalStandard_eq_smul_rootDerivation _ _ _ _ standardColumn_E11_U2

theorem standardColumn_E11_V0_root :
    canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 0) =
      rootDerivation 0 := by
  simpa using canonicalStandard_eq_smul_rootDerivation _ _ _ _ standardColumn_E11_V0

theorem standardColumn_E11_V1_root :
    canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 1) =
      rootDerivation 3 := by
  simpa using canonicalStandard_eq_smul_rootDerivation _ _ _ _ standardColumn_E11_V1

theorem standardColumn_E11_V2_root :
    canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV 2) =
      rootDerivation 8 := by
  simpa using canonicalStandard_eq_smul_rootDerivation _ _ _ _ standardColumn_E11_V2

theorem standardColumn_U0_V1_root :
    canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 1) =
      (-3 : ℝ) • rootDerivation 5 := by
  exact canonicalStandard_eq_smul_rootDerivation _ _ _ _ standardColumn_U0_V1

theorem standardColumn_U0_V2_root :
    canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 2) =
      (-3 : ℝ) • rootDerivation 11 := by
  exact canonicalStandard_eq_smul_rootDerivation _ _ _ _ standardColumn_U0_V2

theorem standardColumn_U1_V0_root :
    canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0) =
      (-3 : ℝ) • rootDerivation 1 := by
  exact canonicalStandard_eq_smul_rootDerivation _ _ _ _ standardColumn_U1_V0

theorem standardColumn_U1_V2_root :
    canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 2) =
      (-3 : ℝ) • rootDerivation 12 := by
  exact canonicalStandard_eq_smul_rootDerivation _ _ _ _ standardColumn_U1_V2

theorem standardColumn_U2_V0_root :
    canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0) =
      (-3 : ℝ) • rootDerivation 2 := by
  exact canonicalStandard_eq_smul_rootDerivation _ _ _ _ standardColumn_U2_V0

theorem standardColumn_U2_V1_root :
    canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1) =
      (-3 : ℝ) • rootDerivation 7 := by
  exact canonicalStandard_eq_smul_rootDerivation _ _ _ _ standardColumn_U2_V1

theorem standardColumn_U0_V0_root :
    canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0) =
      rootDerivation 6 + rootDerivation 13 := by
  apply canonicalParameterLinearEquiv.symm.injective
  rw [standardColumn_U0_V0]
  simp only [rootDerivation, map_add, LinearEquiv.symm_apply_apply]
  funext i
  by_cases hi6 : i = 6 <;> by_cases hi13 : i = 13 <;>
    simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
      hi6, hi13]

theorem standardColumn_U1_V1_root :
    canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1) =
      (-2 : ℝ) • rootDerivation 6 + rootDerivation 13 := by
  apply canonicalParameterLinearEquiv.symm.injective
  rw [standardColumn_U1_V1]
  simp only [rootDerivation, map_add, map_smul, LinearEquiv.symm_apply_apply]
  funext i
  by_cases hi6 : i = 6 <;> by_cases hi13 : i = 13 <;>
    simp [InfoGeometry.Lie.SplitOctonionStandardDerivation.parameterUnit,
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit,
      hi6, hi13]

end InfoGeometry.Lie.SplitOctonionStandardDerivationRootBridge

/-!
# Standard derivations and the native adjoint basis

The standard-derivation coordinate identities and the adjoint basis live in
separate owners.  Their transport is intentionally left downstream until a
proof identifies the two parameter equivalences definitionally or by an
explicit linear equivalence theorem.
-/
