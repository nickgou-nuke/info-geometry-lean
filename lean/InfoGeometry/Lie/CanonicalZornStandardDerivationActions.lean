import Mathlib
import InfoGeometry.Lie.CanonicalZornProductBasis
import InfoGeometry.Lie.CanonicalZornStandardDerivationCovariance

/-!
# Structural actions of the standard derivations on the diagonal corner

These lemmas are deliberately stated through the native product API.  They are
the small algebraic interface used by the opposite-root arguments; no
coordinate expansion of a Zorn matrix is part of their proof.
-/

namespace InfoGeometry.Lie.CanonicalZornStandardDerivationActions

noncomputable section

open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.CanonicalZornProductBasis
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornStandardDerivationCovariance
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

abbrev Der := CanonicalZornDerivation.canonicalZornDerivations

private theorem bracket_apply (D E : Der) (X : CanonicalZornDerivation.CZ) :
    (⁅D, E⁆ : Der).1 X = D.1 (E.1 X) - E.1 (D.1 X) := by
  rfl

theorem bracket_standard_apply
    (a b c d x : CanonicalZornDerivation.CZ) :
    (⁅canonicalStandardDerivationOfCanonical a b,
      canonicalStandardDerivationOfCanonical c d⁆ : Der).1 x =
      directCanonicalStanDerMap
          (directCanonicalStanDerMap a b c) d x +
        directCanonicalStanDerMap c
          (directCanonicalStanDerMap a b d) x := by
  change directCanonicalStanDerMap a b
      (directCanonicalStanDerMap c d x) -
      directCanonicalStanDerMap c d
        (directCanonicalStanDerMap a b x) = _
  have hD : IsDerivation (directCanonicalStanDerMap a b) := by
    rw [← canonicalStandardEnd_transport_eq_direct]
    exact canonicalStandardEnd_isDerivation _ _
  exact standardDerivation_covariant
    (directCanonicalStanDerMap a b)
    hD c d x

theorem bracket_standard_eq
    (a b c d : CanonicalZornDerivation.CZ) :
    ⁅canonicalStandardDerivationOfCanonical a b,
      canonicalStandardDerivationOfCanonical c d⁆ =
      canonicalStandardDerivationOfCanonical
        ((canonicalStandardDerivationOfCanonical a b).1 c) d +
      canonicalStandardDerivationOfCanonical c
        ((canonicalStandardDerivationOfCanonical a b).1 d) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rw [bracket_standard_apply]
  rfl

theorem direct_standard_sub_right
    (a b c x : CanonicalZornDerivation.CZ) :
    directCanonicalStanDerMap a (b - c) x =
      directCanonicalStanDerMap a b x - directCanonicalStanDerMap a c x := by
  rw [directCanonicalStanDerMap_apply,
    directCanonicalStanDerMap_apply, directCanonicalStanDerMap_apply]
  simp only [sub_mul, mul_sub]
  abel

theorem direct_standard_sub_left
    (a b c x : CanonicalZornDerivation.CZ) :
    directCanonicalStanDerMap (a - b) c x =
      directCanonicalStanDerMap a c x - directCanonicalStanDerMap b c x := by
  rw [directCanonicalStanDerMap_apply,
    directCanonicalStanDerMap_apply, directCanonicalStanDerMap_apply]
  simp only [sub_mul, mul_sub]
  abel

theorem direct_standard_zero_left
    (b x : CanonicalZornDerivation.CZ) :
    directCanonicalStanDerMap 0 b x = 0 := by
  rw [directCanonicalStanDerMap_apply]
  simp only [zero_mul, mul_zero, sub_zero, add_zero]

theorem direct_standard_neg_left
    (a b x : CanonicalZornDerivation.CZ) :
    directCanonicalStanDerMap (-a) b x =
      -directCanonicalStanDerMap a b x := by
  rw [← zero_sub a, direct_standard_sub_left,
    direct_standard_zero_left]
  simp

theorem direct_standard_e11_v_e11 (i : Fin 3) :
    directCanonicalStanDerMap canonicalE11 (canonicalV i) canonicalE11 =
      -(canonicalV i) := by
  rw [directCanonicalStanDerMap_apply]
  simp only [e11_mul_v, v_mul_e11, e11_mul_e11,
    mul_zero, zero_mul, zero_sub, sub_self, add_zero]

theorem direct_standard_e11_u_e11 (i : Fin 3) :
    directCanonicalStanDerMap canonicalE11 (canonicalU i) canonicalE11 =
      -(canonicalU i) := by
  rw [directCanonicalStanDerMap_apply]
  simp only [e11_mul_u, u_mul_e11, e11_mul_e11,
    mul_zero, zero_sub, sub_self, add_zero, zero_add]

theorem direct_standard_e11_v_u (i : Fin 3) :
    directCanonicalStanDerMap canonicalE11 (canonicalV i) (canonicalU i) =
      canonicalE11 - canonicalE22 := by
  rw [directCanonicalStanDerMap_apply]
  simp only [e11_mul_v, v_mul_e11, e11_mul_u, u_mul_e11,
    e11_mul_e11, u_mul_v_self, v_mul_u_self,
    e11_mul_e22, e22_mul_e11,
    mul_zero, zero_mul, zero_sub, sub_zero, sub_self,
    add_zero, zero_add, neg_zero, sub_eq_add_neg]
  abel

theorem direct_standard_e11_u_v (i : Fin 3) :
    directCanonicalStanDerMap canonicalE11 (canonicalU i) (canonicalV i) =
      canonicalE11 - canonicalE22 := by
  rw [directCanonicalStanDerMap_apply]
  simp only [e11_mul_u, u_mul_e11, e11_mul_v, v_mul_e11,
    e11_mul_e11, u_mul_v_self, v_mul_u_self,
    e11_mul_e22, e22_mul_e11,
    mul_zero, zero_mul, zero_sub, sub_zero, sub_self,
    add_zero, zero_add, neg_zero, sub_eq_add_neg]

theorem direct_standard_v_u_e (i : Fin 3) :
    directCanonicalStanDerMap (canonicalV i) (canonicalU i) canonicalE11 = 0 := by
  rw [directCanonicalStanDerMap_apply]
  simp only [v_mul_e11, u_mul_e11, v_mul_v_self, e11_mul_u,
    v_mul_u_self, u_mul_v_self, e22_mul_e11, e11_mul_e11,
    e11_mul_v, mul_zero, zero_mul, zero_sub, sub_zero,
    add_zero, zero_add]
  abel

theorem direct_standard_v_u_v (i : Fin 3) :
    directCanonicalStanDerMap (canonicalV i) (canonicalU i) (canonicalV i) =
      2 • canonicalV i := by
  rw [directCanonicalStanDerMap_apply]
  simp only [v_mul_u_self, v_mul_e11, v_mul_v_self,
    u_mul_v_self, e11_mul_v, e22_mul_v, v_mul_e22,
    mul_zero, zero_mul, zero_sub, sub_zero, add_zero, zero_add]
  abel

theorem direct_standard_u_v_e (i : Fin 3) :
    directCanonicalStanDerMap (canonicalU i) (canonicalV i) canonicalE11 = 0 := by
  rw [directCanonicalStanDerMap_apply]
  simp only [u_mul_e11, v_mul_e11, u_mul_u_self, e11_mul_v,
    u_mul_v_self, v_mul_v_self, e22_mul_e11, e11_mul_e11,
    e11_mul_u, mul_zero, zero_mul, zero_sub, sub_zero,
    add_zero, zero_add]
  abel

theorem direct_standard_u_v_u (i : Fin 3) :
    directCanonicalStanDerMap (canonicalU i) (canonicalV i) (canonicalU i) =
      2 • canonicalU i := by
  rw [directCanonicalStanDerMap_apply]
  simp only [u_mul_v_self, v_mul_u_self, u_mul_e11, u_mul_u_self,
    e11_mul_u, e22_mul_u, u_mul_e22, mul_zero, zero_mul,
    zero_sub, sub_zero, add_zero, zero_add]
  abel

theorem direct_standard_e11_e22_u (i : Fin 3) :
    directCanonicalStanDerMap canonicalE11 canonicalE22 (canonicalU i) = 0 := by
  rw [directCanonicalStanDerMap_apply]
  simp only [e11_mul_e22, e22_mul_e11, e11_mul_u, e22_mul_u,
    u_mul_e11, u_mul_e22, mul_zero, zero_mul, zero_sub,
    sub_zero, sub_self, add_zero, zero_add]

theorem direct_standard_e11_e11_u (i : Fin 3) :
    directCanonicalStanDerMap canonicalE11 canonicalE11 (canonicalU i) = 0 := by
  rw [directCanonicalStanDerMap_apply]
  simp only [e11_mul_e11, e11_mul_u, u_mul_e11,
    InfoGeometry.Lie.CanonicalZornProductBasis.e22_mul_e22,
    e22_mul_u, u_mul_e22,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    zero_sub, sub_zero, add_zero, zero_add]
  abel

theorem direct_standard_e11_e22_e :
    directCanonicalStanDerMap canonicalE11 canonicalE22 canonicalE11 =
      0 := by
  rw [directCanonicalStanDerMap_apply]
  simp only [e11_mul_e22, e22_mul_e11, e11_mul_e11,
    InfoGeometry.Lie.CanonicalZornProductBasis.e22_mul_e22,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    zero_sub, sub_zero,
    add_zero, zero_add, sub_eq_add_neg]
  abel

theorem direct_standard_e11_e22_v (i : Fin 3) :
    directCanonicalStanDerMap canonicalE11 canonicalE22 (canonicalV i) = 0 := by
  rw [directCanonicalStanDerMap_apply]
  simp only [e11_mul_e22, e22_mul_e11, e11_mul_v, e22_mul_v,
    v_mul_e11, v_mul_e22, mul_zero, zero_mul, zero_sub,
    sub_zero, add_zero, zero_add]

theorem direct_standard_e11_e11_e :
    directCanonicalStanDerMap canonicalE11 canonicalE11 canonicalE11 = 0 := by
  rw [directCanonicalStanDerMap_apply]
  simp only [e11_mul_e11,
    InfoGeometry.Lie.CanonicalZornProductBasis.e22_mul_e22,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    zero_sub, sub_zero, add_zero, zero_add]
  abel

theorem direct_standard_e11_e11_v (i : Fin 3) :
    directCanonicalStanDerMap canonicalE11 canonicalE11 (canonicalV i) = 0 := by
  rw [directCanonicalStanDerMap_apply]
  simp only [e11_mul_e11, e11_mul_v, v_mul_e11,
    InfoGeometry.Lie.CanonicalZornProductBasis.e22_mul_e22,
    e22_mul_v, v_mul_e22,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    zero_sub, sub_zero, add_zero, zero_add]
  abel

theorem opposite_standard_double_v_u (i : Fin 3) :
    ⁅⁅canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV i),
      -canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU i)⁆,
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV i)⁆ ≠ 0 := by
  intro h
  have h0 := congrArg (fun D : Der => D.1 canonicalE11) h
  dsimp only at h0
  rw [bracket_apply] at h0
  have hinner (x : CanonicalZornDerivation.CZ) :
      (⁅canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV i),
        -canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU i)⁆ : Der).1 x =
        -(directCanonicalStanDerMap
          (directCanonicalStanDerMap canonicalE11 (canonicalV i) canonicalE11)
          (canonicalU i) x +
          directCanonicalStanDerMap canonicalE11
            (directCanonicalStanDerMap canonicalE11 (canonicalV i) (canonicalU i)) x) := by
    rw [bracket_apply]
    change directCanonicalStanDerMap canonicalE11 (canonicalV i)
        (-(directCanonicalStanDerMap canonicalE11 (canonicalU i) x)) -
      (-(directCanonicalStanDerMap canonicalE11 (canonicalU i)
        (directCanonicalStanDerMap canonicalE11 (canonicalV i) x))) = _
    simp only [map_neg]
    have hc := bracket_standard_apply canonicalE11 (canonicalV i)
      canonicalE11 (canonicalU i) x
    change _ = -(directCanonicalStanDerMap
      (directCanonicalStanDerMap canonicalE11 (canonicalV i) canonicalE11)
      (canonicalU i) x +
      directCanonicalStanDerMap canonicalE11
        (directCanonicalStanDerMap canonicalE11 (canonicalV i) (canonicalU i)) x)
    have hcn := congrArg Neg.neg hc
    rw [bracket_apply] at hcn
    simpa only [sub_eq_add_neg, neg_add, neg_neg] using hcn
  simp_rw [hinner] at h0
  change -(directCanonicalStanDerMap
      (directCanonicalStanDerMap canonicalE11 (canonicalV i) canonicalE11)
      (canonicalU i)
      (directCanonicalStanDerMap canonicalE11 (canonicalV i) canonicalE11) +
    directCanonicalStanDerMap canonicalE11
      (directCanonicalStanDerMap canonicalE11 (canonicalV i) (canonicalU i))
      (directCanonicalStanDerMap canonicalE11 (canonicalV i) canonicalE11)) -
    directCanonicalStanDerMap canonicalE11 (canonicalV i)
      (-(directCanonicalStanDerMap
        (directCanonicalStanDerMap canonicalE11 (canonicalV i) canonicalE11)
        (canonicalU i) canonicalE11 +
        directCanonicalStanDerMap canonicalE11
          (directCanonicalStanDerMap canonicalE11 (canonicalV i) (canonicalU i))
          canonicalE11)) = 0 at h0
  rw [direct_standard_e11_v_e11] at h0
  rw [direct_standard_e11_v_u, direct_standard_neg_left] at h0
  simp only [map_neg] at h0
  have hgapv (i : Fin 3) :
      directCanonicalStanDerMap canonicalE11
        (canonicalE11 - canonicalE22) (canonicalV i) = 0 := by
    rw [direct_standard_sub_right,
      direct_standard_e11_e11_v, direct_standard_e11_e22_v]
    simp
  have hgapvi := hgapv i
  rw [hgapvi] at h0
  have hgape :
      directCanonicalStanDerMap canonicalE11
        (canonicalE11 - canonicalE22) canonicalE11 = 0 := by
    rw [direct_standard_sub_right,
      direct_standard_e11_e11_e, direct_standard_e11_e22_e]
    simp
  rw [hgape] at h0
  rw [direct_standard_v_u_v] at h0
  rw [direct_standard_neg_left] at h0
  rw [direct_standard_v_u_e] at h0
  simp only [neg_zero, zero_add] at h0
  rw [map_zero] at h0
  simp only [map_neg, neg_neg, zero_add, add_zero, sub_zero, zero_sub,
    neg_zero, one_smul] at h0
  have hv : (2 : ℕ) • canonicalV i = 0 := by
    exact neg_eq_zero.mp h0
  have hv' := congrArg canonicalVectorEquiv hv
  rw [two_nsmul, canonicalVectorEquiv_add, canonicalVectorEquiv_zero] at hv'
  have hc := congrArg
    (fun X : InfoGeometry.Algebra.ZornVectorMatrix ℝ => X.w i) hv'
  norm_num [canonicalV, InfoGeometry.Algebra.ZornVectorMatrix.V,
    InfoGeometry.Algebra.ZornVectorMatrix.zero,
    InfoGeometry.Algebra.ZornVectorMatrix.add,
    InfoGeometry.Algebra.ZornVec3.basis, canonicalVectorEquiv] at hc

theorem direct_cross_1_5_u0 :
    directCanonicalStanDerMap (canonicalU 1) (canonicalV 0) (canonicalU 0) =
      (3 : ℝ) • canonicalU 1 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_one_mul_v_zero, v_zero_mul_u_one, v_mul_u_self 0,
    u_mul_e22, e22_mul_u, e22_mul_e22, u_mul_v_self, v_mul_v_self,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero]
  module

theorem direct_cross_1_5_v1 :
    directCanonicalStanDerMap (canonicalU 1) (canonicalV 0) (canonicalV 1) =
      -(3 : ℝ) • canonicalV 0 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_one_mul_v_zero, v_zero_mul_u_one, v_zero_mul_v_one,
    u_mul_e22, e22_mul_u, e22_mul_v, v_mul_e22,
    u_mul_v_self, v_mul_u_self, v_mul_v_self,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, neg_mul, mul_neg, neg_smul]
  have hprod : canonicalU 1 * (-canonicalU 2) =
      -canonicalV 0 := by
    rw [← neg_one_smul ℝ (canonicalU 2),
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul,
      u_one_mul_u_two]
    simp
  rw [hprod]
  module

theorem direct_cross_1_5_C_u1 :
    directCanonicalStanDerMap (canonicalU 0) (canonicalV 0) (canonicalU 1) =
      -canonicalU 1 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_mul_v_self 0, v_mul_u_self 0, v_zero_mul_u_one,
    e11_mul_u, u_mul_e11, u_mul_e22, e22_mul_u,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero, sub_mul, mul_sub,
    neg_smul, smul_sub]
  module

theorem direct_cross_1_5_C_v0 :
    directCanonicalStanDerMap (canonicalU 0) (canonicalV 0) (canonicalV 0) =
      -(2 : ℝ) • canonicalV 0 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_mul_v_self 0, v_mul_u_self 0,
    e11_mul_v, v_mul_e11, u_mul_e22, e22_mul_v, v_mul_e22,
    v_mul_v_self, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero, add_mul, mul_add,
    neg_smul, mul_smul_comm, sub_mul, mul_sub]
  module

/-! The obsolete exploratory `2 ↔ 11` block was removed; the live native
    branch appears below after the scalar-linearity lemmas. -/

theorem standard_smul_left (r : ℝ) (a b : CanonicalZornDerivation.CZ) :
    canonicalStandardDerivationOfCanonical (r • a) b =
      r • canonicalStandardDerivationOfCanonical a b := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change directCanonicalStanDerMap (r • a) b x = _
  rw [directCanonicalStanDerMap_apply]
  change _ = r • directCanonicalStanDerMap a b x
  rw [directCanonicalStanDerMap_apply]
  simp only [smul_mul, mul_smul, smul_sub, smul_add, smul_smul]

theorem standard_smul_right (r : ℝ) (a b : CanonicalZornDerivation.CZ) :
    canonicalStandardDerivationOfCanonical a (r • b) =
      r • canonicalStandardDerivationOfCanonical a b := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change directCanonicalStanDerMap a (r • b) x = _
  rw [directCanonicalStanDerMap_apply]
  change _ = r • directCanonicalStanDerMap a b x
  rw [directCanonicalStanDerMap_apply]
  simp only [smul_mul, mul_smul, smul_sub, smul_add, smul_smul]

theorem opposite_standard_double_u_v (i : Fin 3) :
    ⁅⁅-canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU i),
      canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV i)⁆,
      -canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU i)⁆ ≠ 0 := by
  have hneg :
      -canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU i) =
        canonicalStandardDerivationOfCanonical (-canonicalE11) (canonicalU i) := by
    simpa only [neg_one_smul, one_smul] using
      (standard_smul_left (-1 : ℝ) canonicalE11 (canonicalU i)).symm
  have h0 :
      (canonicalStandardDerivationOfCanonical (-canonicalE11) (canonicalU i)).1
        canonicalE11 = canonicalU i := by
    change directCanonicalStanDerMap (-canonicalE11) (canonicalU i) canonicalE11 = _
    rw [direct_standard_neg_left, direct_standard_e11_u_e11]
    simp
  have h1 :
      (canonicalStandardDerivationOfCanonical (-canonicalE11) (canonicalU i)).1
        (canonicalV i) = -(canonicalE11 - canonicalE22) := by
    change directCanonicalStanDerMap (-canonicalE11) (canonicalU i) (canonicalV i) = _
    rw [direct_standard_neg_left, direct_standard_e11_u_v]
  have hC :
      ⁅-canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU i),
        canonicalStandardDerivationOfCanonical canonicalE11 (canonicalV i)⁆ =
      canonicalStandardDerivationOfCanonical (canonicalU i) (canonicalV i) -
        canonicalStandardDerivationOfCanonical canonicalE11
          (canonicalE11 - canonicalE22) := by
    rw [hneg, bracket_standard_eq, h0, h1,
      ← neg_one_smul ℝ (canonicalE11 - canonicalE22), standard_smul_right]
    module
  have hs0 :
      (canonicalStandardDerivationOfCanonical (canonicalU i) (canonicalV i)).1
        (-canonicalE11) = 0 := by
    change directCanonicalStanDerMap (canonicalU i) (canonicalV i) (-canonicalE11) = 0
    rw [map_neg, direct_standard_u_v_e]
    simp
  have hs1 :
      (canonicalStandardDerivationOfCanonical (canonicalU i) (canonicalV i)).1
        (canonicalU i) = 2 • canonicalU i := by
    change directCanonicalStanDerMap (canonicalU i) (canonicalV i) (canonicalU i) = _
    exact direct_standard_u_v_u i
  have hc0 :
      (canonicalStandardDerivationOfCanonical canonicalE11 (canonicalE11 - canonicalE22)).1
        (-canonicalE11) = 0 := by
    change directCanonicalStanDerMap canonicalE11 (canonicalE11 - canonicalE22)
      (-canonicalE11) = 0
    rw [map_neg, direct_standard_sub_right,
      direct_standard_e11_e11_e, direct_standard_e11_e22_e]
    simp
  have hc1 :
      (canonicalStandardDerivationOfCanonical canonicalE11 (canonicalE11 - canonicalE22)).1
        (canonicalU i) = 0 := by
    change directCanonicalStanDerMap canonicalE11 (canonicalE11 - canonicalE22)
      (canonicalU i) = 0
    rw [direct_standard_sub_right,
      direct_standard_e11_e11_u, direct_standard_e11_e22_u]
    simp
  have hbrC :
      ⁅canonicalStandardDerivationOfCanonical canonicalE11 (canonicalE11 - canonicalE22),
        canonicalStandardDerivationOfCanonical (-canonicalE11) (canonicalU i)⁆ = 0 := by
    rw [bracket_standard_eq, hc0, hc1]
    have hz1 : canonicalStandardDerivationOfCanonical 0 (canonicalU i) = 0 := by
      rw [← zero_smul ℝ canonicalE11, standard_smul_left]
      simp
    have hz2 : canonicalStandardDerivationOfCanonical (-canonicalE11) 0 = 0 := by
      rw [← zero_smul ℝ (canonicalU i), standard_smul_right]
      simp
    rw [hz1, hz2, add_zero]
  have hOuter :
      ⁅canonicalStandardDerivationOfCanonical (canonicalU i) (canonicalV i) -
          canonicalStandardDerivationOfCanonical canonicalE11
            (canonicalE11 - canonicalE22),
        -canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU i)⁆ =
        (2 : ℕ) • (-canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU i)) := by
    rw [sub_lie, hneg, bracket_standard_eq, hs0, hs1, hbrC]
    have hscaleNat :
        canonicalStandardDerivationOfCanonical (-canonicalE11) ((2 : ℕ) • canonicalU i) =
          (2 : ℕ) • canonicalStandardDerivationOfCanonical (-canonicalE11) (canonicalU i) := by
      simpa only [two_nsmul, two_smul] using
        (standard_smul_right (2 : ℝ) (-canonicalE11) (canonicalU i))
    rw [hscaleNat]
    have hz : canonicalStandardDerivationOfCanonical 0 (canonicalU i) = 0 := by
      rw [← zero_smul ℝ canonicalE11, standard_smul_left]
      simp
    rw [hz]
    simp
  rw [hC, hOuter]
  intro h
  have h0 := congrArg (fun D : Der => D.1 canonicalE11) h
  dsimp only at h0
  change (2 : ℕ) •
      ((-canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU i)).1 canonicalE11) = 0 at h0
  rw [show (-canonicalStandardDerivationOfCanonical canonicalE11 (canonicalU i)).1 canonicalE11 =
      canonicalU i by
    change -directCanonicalStanDerMap canonicalE11 (canonicalU i) canonicalE11 = _
    rw [direct_standard_e11_u_e11]
    simp] at h0
  have hv := congrArg canonicalVectorEquiv h0
  rw [two_nsmul, canonicalVectorEquiv_add, canonicalVectorEquiv_zero] at hv
  have hw := congrArg
    (fun X : InfoGeometry.Algebra.ZornVectorMatrix ℝ => X.v i) hv
  norm_num [canonicalU, InfoGeometry.Algebra.ZornVectorMatrix.U,
    InfoGeometry.Algebra.ZornVectorMatrix.zero,
    InfoGeometry.Algebra.ZornVectorMatrix.add,
    InfoGeometry.Algebra.ZornVec3.basis, canonicalVectorEquiv] at hw

/-! The `2 ↔ 11` cross-root action, kept live in the structural owner.
These are consequences of the canonical-vector multiplication API; no
matrix-entry expansion is used. -/

theorem direct_cross_2_11_u0 :
    directCanonicalStanDerMap (canonicalU 2) (canonicalV 0) (canonicalU 0) =
      (3 : ℝ) • canonicalU 2 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_two_mul_v_zero, v_zero_mul_u_two, v_mul_u_self 0,
    u_mul_e22, e22_mul_u, e22_mul_e22, u_mul_v_self, v_mul_v_self,
    u_two_mul_u_zero, u_mul_e11, e11_mul_u,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero]
  module

theorem direct_cross_2_11_v2 :
    directCanonicalStanDerMap (canonicalU 2) (canonicalV 0) (canonicalV 2) =
      -(3 : ℝ) • canonicalV 0 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_two_mul_v_zero, v_zero_mul_u_two, v_zero_mul_v_two,
    u_mul_e22, e22_mul_u, e22_mul_v, v_mul_e22,
    u_mul_v_self, v_mul_u_self, v_mul_v_self,
    u_two_mul_u_zero, u_zero_mul_u_two,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, neg_mul, mul_neg, neg_smul]
  rw [u_two_mul_u_one]
  module

theorem direct_cross_2_11_S_u2 :
    directCanonicalStanDerMap (canonicalU 2) (canonicalV 2) (canonicalU 2) =
      (2 : ℝ) • canonicalU 2 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_mul_v_self 2, v_mul_u_self 2, e11_mul_u, e22_mul_u,
    u_mul_e11, u_mul_e22, e11_mul_e11, e22_mul_e22,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero, sub_mul, mul_sub,
    smul_sub]
  module

theorem direct_cross_2_11_S_v0 :
    directCanonicalStanDerMap (canonicalU 2) (canonicalV 2) (canonicalV 0) =
      canonicalV 0 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_mul_v_self 2, v_mul_u_self 2, v_zero_mul_v_two,
    e11_mul_v, e22_mul_v, v_mul_e11, v_mul_e22,
    u_mul_v_self, v_mul_u_self, u_two_mul_u_one, u_two_mul_u_zero,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero, sub_mul, mul_sub,
    smul_sub, neg_smul]
  rw [v_two_mul_v_zero,
    ← neg_one_smul ℝ (canonicalU 1),
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul,
    u_two_mul_u_one]
  module

theorem direct_cross_2_11_C_u2 :
    directCanonicalStanDerMap (canonicalU 0) (canonicalV 0) (canonicalU 2) =
      -canonicalU 2 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_mul_v_self 0, v_mul_u_self 0, v_zero_mul_u_two,
    e11_mul_u, u_mul_e11, u_mul_e22, e22_mul_u,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero, sub_mul, mul_sub,
    neg_smul, smul_sub]
  module

theorem direct_cross_2_11_C_v0 :
    directCanonicalStanDerMap (canonicalU 0) (canonicalV 0) (canonicalV 0) =
      -(2 : ℝ) • canonicalV 0 := direct_cross_1_5_C_v0

theorem standard_bracket_cross_2_11 :
    ⁅canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0),
      canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 2)⁆ =
      (3 : ℝ) • canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2) -
        (3 : ℝ) • canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0) := by
  have hA0 :
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0)).1
        (canonicalU 0) = (3 : ℝ) • canonicalU 2 := direct_cross_2_11_u0
  have hA1 :
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0)).1
        (canonicalV 2) = -(3 : ℝ) • canonicalV 0 := direct_cross_2_11_v2
  rw [bracket_standard_eq, hA0, hA1, standard_smul_left, standard_smul_right]
  module

theorem standard_bracket_S_A_cross_2_11 :
    ⁅canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2),
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0)⁆ =
      (3 : ℝ) • canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0) := by
  have hS0 :
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)).1
        (canonicalU 2) = (2 : ℝ) • canonicalU 2 := direct_cross_2_11_S_u2
  have hS1 :
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)).1
        (canonicalV 0) = canonicalV 0 := direct_cross_2_11_S_v0
  rw [bracket_standard_eq, hS0, hS1, standard_smul_left]
  module

theorem standard_bracket_C_A_cross_2_11 :
    ⁅canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0),
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0)⁆ =
      -(3 : ℝ) • canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0) := by
  have hC0 :
      (canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0)).1
        (canonicalU 2) = -canonicalU 2 := direct_cross_2_11_C_u2
  have hC1 :
      (canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0)).1
        (canonicalV 0) = -(2 : ℝ) • canonicalV 0 := direct_cross_2_11_C_v0
  rw [bracket_standard_eq, hC0, hC1,
    ← neg_one_smul ℝ (canonicalU 2), standard_smul_left,
    standard_smul_right]
  module

theorem opposite_standard_double_cross_2_11 :
    ⁅⁅canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0),
      canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 2)⁆,
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0)⁆ ≠ 0 := by
  have hA :
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 0) ≠ 0 := by
    intro h
    have h0 := congrArg (fun D : Der => D.1 (canonicalU 0)) h
    change directCanonicalStanDerMap (canonicalU 2) (canonicalV 0) (canonicalU 0) = 0 at h0
    rw [direct_cross_2_11_u0] at h0
    have hv := congrArg canonicalVectorEquiv h0
    simp only [canonicalVectorEquiv_zero, canonicalVectorEquiv_smul] at hv
    have hu := congrArg
      (fun X : InfoGeometry.Algebra.ZornVectorMatrix ℝ => X.v 2) hv
    norm_num [canonicalU, InfoGeometry.Algebra.ZornVectorMatrix.U,
      InfoGeometry.Algebra.ZornVectorMatrix.zero,
      InfoGeometry.Algebra.ZornVectorMatrix.smul,
      InfoGeometry.Algebra.ZornVec3.basis,
      InfoGeometry.Canonical.ZornMatrix.coordEquiv, canonicalVectorEquiv] at hu
  rw [standard_bracket_cross_2_11, sub_lie, smul_lie, smul_lie,
    standard_bracket_S_A_cross_2_11, standard_bracket_C_A_cross_2_11]
  convert smul_ne_zero (by norm_num : (18 : ℝ) ≠ 0) hA using 1 <;>
    module

/-! The `7 ↔ 12` cross-root action, reduced to the native product table. -/

theorem direct_cross_7_12_u1 :
    directCanonicalStanDerMap (canonicalU 2) (canonicalV 1) (canonicalU 1) =
      (3 : ℝ) • canonicalU 2 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_two_mul_v_one, v_one_mul_u_two, v_mul_u_self 1,
    u_mul_e22, e22_mul_u, e22_mul_e22, u_mul_v_self, v_mul_v_self,
    u_two_mul_u_one, u_mul_e11, e11_mul_u,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero]
  module

theorem direct_cross_7_12_v2 :
    directCanonicalStanDerMap (canonicalU 2) (canonicalV 1) (canonicalV 2) =
      -(3 : ℝ) • canonicalV 1 := by
  have hprod : canonicalU 2 * -canonicalU 0 = -canonicalV 1 := by
    rw [← neg_one_smul ℝ (canonicalU 0),
      InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_smul,
      u_two_mul_u_zero]
    simp
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_two_mul_v_one, v_one_mul_u_two, v_one_mul_v_two, e11_mul_v, e22_mul_v,
    v_mul_e11, v_mul_e22, u_mul_v_self, v_mul_u_self,
    u_two_mul_u_one, u_one_mul_u_two,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero,
    smul_sub, neg_smul, mul_neg, neg_mul]
  rw [hprod]
  module

theorem direct_cross_7_12_S_u2 :
    directCanonicalStanDerMap (canonicalU 2) (canonicalV 2) (canonicalU 2) =
      (2 : ℝ) • canonicalU 2 := direct_cross_2_11_S_u2

theorem direct_cross_7_12_S_v1 :
    directCanonicalStanDerMap (canonicalU 2) (canonicalV 2) (canonicalV 1) =
      canonicalV 1 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_mul_v_self, v_mul_u_self, v_two_mul_v_one,
    u_two_mul_u_zero, u_two_mul_v_one, v_one_mul_u_two,
    v_one_mul_v_two, u_zero_mul_u_two,
    e11_mul_v, e22_mul_v, v_mul_e11, v_mul_e22,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    sub_mul, mul_sub, smul_sub, sub_zero, zero_sub, add_zero, zero_add,
    smul_zero, neg_mul, mul_neg, neg_smul]
  module

theorem direct_cross_7_12_C_u2 :
    directCanonicalStanDerMap (canonicalU 1) (canonicalV 1) (canonicalU 2) =
      -canonicalU 2 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_mul_v_self 1, v_mul_u_self 1, v_one_mul_u_two,
    e11_mul_u, u_mul_e11, u_mul_e22, e22_mul_u,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero, sub_mul, mul_sub,
    neg_smul, smul_sub]
  module

theorem direct_cross_7_12_C_v1 :
    directCanonicalStanDerMap (canonicalU 1) (canonicalV 1) (canonicalV 1) =
      -(2 : ℝ) • canonicalV 1 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_mul_v_self 1, v_mul_u_self 1, v_mul_v_self 1,
    e11_mul_v, e22_mul_v, v_mul_e11, v_mul_e22,
    u_mul_v_self, v_mul_u_self, u_mul_e11, u_mul_e22,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero, sub_mul, mul_sub,
    neg_smul, smul_sub]
  module

theorem standard_bracket_cross_7_12 :
    ⁅canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1),
      canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 2)⁆ =
      (3 : ℝ) • canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2) -
        (3 : ℝ) • canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1) := by
  have hA0 :
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1)).1
        (canonicalU 1) = (3 : ℝ) • canonicalU 2 := by
    change directCanonicalStanDerMap (canonicalU 2) (canonicalV 1)
      (canonicalU 1) = _
    exact direct_cross_7_12_u1
  have hA1 :
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1)).1
        (canonicalV 2) = -(3 : ℝ) • canonicalV 1 := by
    change directCanonicalStanDerMap (canonicalU 2) (canonicalV 1)
      (canonicalV 2) = _
    exact direct_cross_7_12_v2
  rw [bracket_standard_eq, hA0, hA1, standard_smul_left, standard_smul_right]
  module

theorem standard_bracket_S_A_cross_7_12 :
    ⁅canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2),
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1)⁆ =
      (3 : ℝ) • canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1) := by
  have hS2 :
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)).1
        (canonicalU 2) = (2 : ℝ) • canonicalU 2 := by
    change directCanonicalStanDerMap (canonicalU 2) (canonicalV 2)
      (canonicalU 2) = _
    exact direct_cross_7_12_S_u2
  have hS1 :
      (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 2)).1
        (canonicalV 1) = canonicalV 1 := by
    change directCanonicalStanDerMap (canonicalU 2) (canonicalV 2)
      (canonicalV 1) = _
    exact direct_cross_7_12_S_v1
  rw [bracket_standard_eq, hS2, hS1, standard_smul_left]
  module

theorem standard_bracket_C_A_cross_7_12 :
    ⁅canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1),
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1)⁆ =
      -(3 : ℝ) • canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1) := by
  have hC2 :
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1)).1
        (canonicalU 2) = -canonicalU 2 := by
    change directCanonicalStanDerMap (canonicalU 1) (canonicalV 1)
      (canonicalU 2) = _
    exact direct_cross_7_12_C_u2
  have hC1 :
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1)).1
        (canonicalV 1) = -(2 : ℝ) • canonicalV 1 := by
    change directCanonicalStanDerMap (canonicalU 1) (canonicalV 1)
      (canonicalV 1) = _
    exact direct_cross_7_12_C_v1
  rw [bracket_standard_eq, hC2, hC1,
    ← neg_one_smul ℝ (canonicalU 2), standard_smul_left, standard_smul_right]
  module

theorem opposite_standard_double_cross_7_12 :
    ⁅⁅canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1),
      canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 2)⁆,
      canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1)⁆ ≠ 0 := by
  rw [standard_bracket_cross_7_12, sub_lie, smul_lie, smul_lie,
    standard_bracket_S_A_cross_7_12, standard_bracket_C_A_cross_7_12]
  convert smul_ne_zero (by norm_num : (18 : ℝ) ≠ 0) (by
    intro h
    have h0 := congrArg (fun D : Der => D.1 (canonicalU 1)) h
    change (canonicalStandardDerivationOfCanonical (canonicalU 2) (canonicalV 1)).1
      (canonicalU 1) = 0 at h0
    change directCanonicalStanDerMap (canonicalU 2) (canonicalV 1)
      (canonicalU 1) = 0 at h0
    rw [direct_cross_7_12_u1] at h0
    have hv := congrArg canonicalVectorEquiv h0
    simp only [canonicalVectorEquiv_zero, canonicalVectorEquiv_smul] at hv
    have hu := congrArg
      (fun X : InfoGeometry.Algebra.ZornVectorMatrix ℝ => X.v 2) hv
    norm_num [canonicalU, InfoGeometry.Algebra.ZornVectorMatrix.U,
      InfoGeometry.Algebra.ZornVectorMatrix.zero,
      InfoGeometry.Algebra.ZornVectorMatrix.smul,
      InfoGeometry.Algebra.ZornVec3.basis, canonicalVectorEquiv] at hu) using 1 <;>
    module

theorem standard_bracket_cross_1_5 :
    ⁅canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0),
      canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 1)⁆ =
      (3 : ℝ) • canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1) -
        (3 : ℝ) • canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0) := by
  have hA0 :
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0)).1
        (canonicalU 0) = (3 : ℝ) • canonicalU 1 := by
    change directCanonicalStanDerMap (canonicalU 1) (canonicalV 0)
      (canonicalU 0) = _
    exact direct_cross_1_5_u0
  have hA1 :
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0)).1
        (canonicalV 1) = -(3 : ℝ) • canonicalV 0 := by
    change directCanonicalStanDerMap (canonicalU 1) (canonicalV 0)
      (canonicalV 1) = _
    exact direct_cross_1_5_v1
  rw [bracket_standard_eq, hA0, hA1, standard_smul_left, standard_smul_right]
  module

theorem direct_cross_1_5_S_u1 :
    directCanonicalStanDerMap (canonicalU 1) (canonicalV 1) (canonicalU 1) =
      (2 : ℝ) • canonicalU 1 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_mul_v_self 1, v_mul_u_self 1, e11_mul_u, e22_mul_u,
    u_mul_e11, u_mul_e22, e11_mul_e11, e22_mul_e22,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero, sub_mul, mul_sub,
    smul_sub]
  module

theorem direct_cross_1_5_S_v0 :
    directCanonicalStanDerMap (canonicalU 1) (canonicalV 1) (canonicalV 0) =
      canonicalV 0 := by
  rw [directCanonicalStanDerMap_apply_normal_form]
  simp only [u_mul_v_self 1, v_mul_u_self 1, v_one_mul_v_zero,
    e11_mul_v, e22_mul_v, v_mul_e11, v_mul_e22,
    u_mul_v_self, v_mul_u_self, u_one_mul_u_two,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_zero,
    zero_sub, sub_zero, add_zero, zero_add, smul_zero, sub_mul, mul_sub,
    smul_sub, neg_smul]
  module

theorem standard_bracket_S_A_cross_1_5 :
    ⁅canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1),
      canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0)⁆ =
      (3 : ℝ) • canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0) := by
  have hS1 :
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1)).1
        (canonicalU 1) = (2 : ℝ) • canonicalU 1 := by
    change directCanonicalStanDerMap (canonicalU 1) (canonicalV 1)
      (canonicalU 1) = _
    exact direct_cross_1_5_S_u1
  have hS0 :
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 1)).1
        (canonicalV 0) = canonicalV 0 := by
    change directCanonicalStanDerMap (canonicalU 1) (canonicalV 1)
      (canonicalV 0) = _
    exact direct_cross_1_5_S_v0
  rw [bracket_standard_eq, hS1, hS0, standard_smul_left]
  module

theorem standard_bracket_C_A_cross_1_5 :
    ⁅canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0),
      canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0)⁆ =
      -(3 : ℝ) • canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0) := by
  have hC1 :
      (canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0)).1
        (canonicalU 1) = -canonicalU 1 := by
    change directCanonicalStanDerMap (canonicalU 0) (canonicalV 0)
      (canonicalU 1) = _
    exact direct_cross_1_5_C_u1
  have hC0 :
      (canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 0)).1
        (canonicalV 0) = -(2 : ℝ) • canonicalV 0 := by
    change directCanonicalStanDerMap (canonicalU 0) (canonicalV 0)
      (canonicalV 0) = _
    exact direct_cross_1_5_C_v0
  rw [bracket_standard_eq, hC1, hC0,
    ← neg_one_smul ℝ (canonicalU 1), standard_smul_left,
    standard_smul_right]
  module

theorem opposite_standard_double_cross_1_5 :
    ⁅⁅canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0),
      canonicalStandardDerivationOfCanonical (canonicalU 0) (canonicalV 1)⁆,
      canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0)⁆ ≠ 0 := by
  rw [standard_bracket_cross_1_5, sub_lie, smul_lie, smul_lie,
    standard_bracket_S_A_cross_1_5, standard_bracket_C_A_cross_1_5]
  intro h
  norm_num [smul_smul, sub_eq_add_neg, add_smul] at h
  have h0 := congrArg (fun D : Der => D.1 (canonicalU 0)) h
  dsimp only at h0
  change (9 : ℝ) •
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0)).1
        (canonicalU 0) + (9 : ℝ) •
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0)).1
        (canonicalU 0) = 0 at h0
  have hA :
      (canonicalStandardDerivationOfCanonical (canonicalU 1) (canonicalV 0)).1 =
        directCanonicalStanDerMap (canonicalU 1) (canonicalV 0) := rfl
  rw [hA] at h0
  rw [direct_cross_1_5_u0] at h0
  have hv := congrArg canonicalVectorEquiv h0
  simp only [canonicalVectorEquiv_add, canonicalVectorEquiv_smul,
    canonicalVectorEquiv_zero] at hv
  have hc := congrArg
    (fun X : InfoGeometry.Algebra.ZornVectorMatrix ℝ => X.v 1) hv
  norm_num [canonicalU, InfoGeometry.Algebra.ZornVectorMatrix.U,
    InfoGeometry.Algebra.ZornVectorMatrix.zero,
    InfoGeometry.Algebra.ZornVectorMatrix.add,
    InfoGeometry.Algebra.ZornVectorMatrix.smul,
    InfoGeometry.Algebra.ZornVec3.basis,
    InfoGeometry.Canonical.ZornMatrix.coordEquiv, canonicalVectorEquiv] at hc

end
