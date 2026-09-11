import InfoGeometry.Lie.SplitOctonionStandardDerivation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Canonical products of the Zorn basis elements

The standard-derivation covariance theorem uses only these basis products.
They are transported from the native `ZornVectorMatrix` API through the
canonical linear equivalence; no coordinate expansion of canonical Zorn
matrices is used here.
-/

namespace InfoGeometry.Lie.CanonicalZornProductBasis

open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.ZornVectorMatrix

noncomputable abbrev canonicalE22 : InfoGeometry.Canonical.ZornMatrix ℝ :=
  canonicalVectorEquiv.symm E22

private lemma map_prod (x y : InfoGeometry.Canonical.ZornMatrix ℝ) :
    canonicalVectorEquiv (x * y) =
      InfoGeometry.Algebra.ZornVectorMatrix.mul
        (canonicalVectorEquiv x) (canonicalVectorEquiv y) :=
  canonicalVectorEquiv_mul x y

theorem e11_mul_e11 : canonicalE11 * canonicalE11 = canonicalE11 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact E11_mul_E11

theorem e11_mul_e22 : canonicalE11 * canonicalE22 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact E11_mul_E22

theorem e22_mul_e11 : canonicalE22 * canonicalE11 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact E22_mul_E11

theorem e22_mul_e22 : canonicalE22 * canonicalE22 = canonicalE22 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact E22_mul_E22

theorem e22_mul_u (i : Fin 3) : canonicalE22 * canonicalU i = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  change mul E22 (U i) = zero
  ext j <;> simp [mul, E22, U, zero,
    InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross]

theorem u_mul_e22 (i : Fin 3) : canonicalU i * canonicalE22 = canonicalU i := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  change mul (U i) E22 = U i
  ext j <;> simp [mul, E22, U,
    InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross]

theorem e22_mul_v (i : Fin 3) : canonicalE22 * canonicalV i = canonicalV i := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  change mul E22 (V i) = V i
  ext j <;> simp [mul, E22, V,
    InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross]

theorem v_mul_e22 (i : Fin 3) : canonicalV i * canonicalE22 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  change mul (V i) E22 = zero
  ext j <;> simp [mul, E22, V, zero,
    InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross]

theorem e11_mul_u (i : Fin 3) : canonicalE11 * canonicalU i = canonicalU i := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  change mul E11 (U i) = U i
  ext j <;> simp [mul, E11, U,
    InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross]

theorem u_mul_e11 (i : Fin 3) : canonicalU i * canonicalE11 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  change mul (U i) E11 = zero
  ext j <;> simp [mul, E11, U, zero,
    InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross]

theorem e11_mul_v (i : Fin 3) : canonicalE11 * canonicalV i = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  change mul E11 (V i) = zero
  ext j <;> simp [mul, E11, V, zero,
    InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross]

theorem v_mul_e11 (i : Fin 3) : canonicalV i * canonicalE11 = canonicalV i := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  change mul (V i) E11 = V i
  ext j <;> simp [mul, E11, V,
    InfoGeometry.Algebra.ZornVec3.dot, InfoGeometry.Algebra.ZornVec3.cross]

theorem u_mul_v_self (i : Fin 3) : canonicalU i * canonicalV i = canonicalE11 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_mul_V_self i

theorem v_mul_u_self (i : Fin 3) : canonicalV i * canonicalU i = canonicalE22 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_mul_U_self i

theorem u_mul_u_self (i : Fin 3) : canonicalU i * canonicalU i = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_mul_self_zero i

theorem v_mul_v_self (i : Fin 3) : canonicalV i * canonicalV i = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_mul_self_zero i

theorem u_one_mul_v_zero : canonicalU 1 * canonicalV 0 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_one_mul_V_zero

theorem u_zero_mul_v_one : canonicalU 0 * canonicalV 1 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_zero_mul_V_one

theorem u_two_mul_v_zero : canonicalU 2 * canonicalV 0 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_two_mul_V_zero

theorem u_one_mul_v_two : canonicalU 1 * canonicalV 2 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_one_mul_V_two

theorem u_two_mul_v_one : canonicalU 2 * canonicalV 1 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_two_mul_V_one

theorem v_zero_mul_u_one : canonicalV 0 * canonicalU 1 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_zero_mul_U_one

theorem v_zero_mul_u_two : canonicalV 0 * canonicalU 2 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_zero_mul_U_two

theorem v_one_mul_u_zero : canonicalV 1 * canonicalU 0 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_one_mul_U_zero

theorem v_one_mul_u_two : canonicalV 1 * canonicalU 2 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_one_mul_U_two

theorem v_two_mul_u_zero : canonicalV 2 * canonicalU 0 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_two_mul_U_zero

theorem v_two_mul_u_one : canonicalV 2 * canonicalU 1 = 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_two_mul_U_one

theorem u_zero_mul_u_one : canonicalU 0 * canonicalU 1 = canonicalV 2 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_zero_mul_U_one

theorem u_one_mul_u_zero : canonicalU 1 * canonicalU 0 = -canonicalV 2 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_one_mul_U_zero

theorem u_one_mul_u_two : canonicalU 1 * canonicalU 2 = canonicalV 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_one_mul_U_two

theorem u_two_mul_u_one : canonicalU 2 * canonicalU 1 = -canonicalV 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_two_mul_U_one

theorem u_two_mul_u_zero : canonicalU 2 * canonicalU 0 = canonicalV 1 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_two_mul_U_zero

theorem u_zero_mul_u_two : canonicalU 0 * canonicalU 2 = -canonicalV 1 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact U_zero_mul_U_two

theorem v_zero_mul_v_one : canonicalV 0 * canonicalV 1 = -canonicalU 2 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_zero_mul_V_one

theorem v_one_mul_v_zero : canonicalV 1 * canonicalV 0 = canonicalU 2 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_one_mul_V_zero

theorem v_one_mul_v_two : canonicalV 1 * canonicalV 2 = -canonicalU 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_one_mul_V_two

theorem v_two_mul_v_one : canonicalV 2 * canonicalV 1 = canonicalU 0 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_two_mul_V_one

theorem v_two_mul_v_zero : canonicalV 2 * canonicalV 0 = -canonicalU 1 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_two_mul_V_zero

theorem v_zero_mul_v_two : canonicalV 0 * canonicalV 2 = canonicalU 1 := by
  apply canonicalVectorEquiv.injective
  rw [map_prod]
  exact V_zero_mul_V_two

attribute [simp] u_one_mul_v_zero u_zero_mul_v_one u_two_mul_v_zero
  u_one_mul_v_two u_two_mul_v_one v_zero_mul_u_one v_zero_mul_u_two v_one_mul_u_zero
  v_one_mul_u_two v_two_mul_u_zero v_two_mul_u_one
  u_zero_mul_u_one u_one_mul_u_zero u_one_mul_u_two u_two_mul_u_one
  u_two_mul_u_zero u_zero_mul_u_two v_zero_mul_v_one v_one_mul_v_zero
  v_one_mul_v_two v_two_mul_v_one v_two_mul_v_zero v_zero_mul_v_two

end InfoGeometry.Lie.CanonicalZornProductBasis
