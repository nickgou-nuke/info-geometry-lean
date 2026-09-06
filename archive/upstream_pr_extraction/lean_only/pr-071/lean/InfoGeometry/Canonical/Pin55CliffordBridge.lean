import InfoGeometry.Clifford.ConformalGeneratorLemmas55
import InfoGeometry.Clifford.ConformalLieAlgebra55Dilation
import InfoGeometry.Clifford.SpinorRep
import InfoGeometry.Canonical.Herm2x2OsO55RationalBridge

namespace InfoGeometry.Canonical.Pin55CliffordBridge

open InfoGeometry.Clifford.ConformalLift55
open InfoGeometry.Clifford.ConformalLieAlgebra55

theorem two_smul_D5 :
    (2 : ℝ) • D5 = u5 * v5 - v5 * u5 := by
  dsimp [D5]
  rw [smul_smul]
  norm_num

theorem two_smul_D4 :
    (2 : ℝ) • D4 = u4 * v4 - v4 * u4 := by
  dsimp [D4]
  rw [smul_smul]
  norm_num

theorem nullPair_phase_factorization
    {A : Type*} [Ring A] (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hcar : u * v + v * u = 1) :
    u - v = (u * v - v * u) * (u + v) := by
  have huv : u * v * u = u := by
    calc
      u * v * u = (u * v + v * u) * u := by
        rw [add_mul, mul_assoc v u u, hu, mul_zero, add_zero]
      _ = 1 * u := by rw [hcar]
      _ = u := one_mul _
  have vuv : v * u * v = v := by
    calc
      v * u * v = (u * v + v * u) * v := by
        rw [add_mul, mul_assoc u v v, hv, mul_zero, zero_add]
      _ = 1 * v := by rw [hcar]
      _ = v := one_mul _
  calc
    u - v = u * v * u - v * u * v := by rw [huv, vuv]
    _ = (u * v - v * u) * (u + v) := by
      simp only [sub_mul, mul_add]
      rw [mul_assoc u v v, hv, mul_zero,
        mul_assoc v u u, hu, mul_zero]
      abel

theorem nullPair_phase_reverse_factorization
    {A : Type*} [Ring A] (u v : A)
    (hu : u * u = 0) (hv : v * v = 0)
    (hcar : u * v + v * u = 1) :
    (u + v) * (u * v - v * u) = -(u - v) := by
  have huv : u * v * u = u := by
    calc
      u * v * u = (u * v + v * u) * u := by
        rw [add_mul, mul_assoc v u u, hu, mul_zero, add_zero]
      _ = 1 * u := by rw [hcar]
      _ = u := one_mul _
  have vuv : v * u * v = v := by
    calc
      v * u * v = (u * v + v * u) * v := by
        rw [add_mul, mul_assoc u v v, hv, mul_zero, zero_add]
      _ = 1 * v := by rw [hcar]
      _ = v := one_mul _
  calc
    (u + v) * (u * v - v * u) =
        u * u * v - u * v * u + v * u * v - v * v * u := by
      noncomm_ring
    _ = -(u - v) := by
      rw [hu, zero_mul, hv, zero_mul,
        huv, vuv]
      abel

lemma u5_v5_u5 :
    u5 * v5 * u5 = u5 := by
  calc
    u5 * v5 * u5
        = (u5 * v5 + v5 * u5) * u5 := by
            rw [add_mul]
            rw [mul_assoc v5 u5 u5, InfoGeometry.Clifford.ConformalLieAlgebra55.u5_sq,
              mul_zero, add_zero]
    _ = 1 * u5 := by
      rw [InfoGeometry.Clifford.ConformalLieAlgebra55.u5_v5_add_v5_u5]
    _ = u5 := one_mul _

lemma v5_u5_v5 :
    v5 * u5 * v5 = v5 := by
  calc
    v5 * u5 * v5
        = (u5 * v5 + v5 * u5) * v5 := by
            rw [add_mul]
            rw [mul_assoc u5 v5 v5, InfoGeometry.Clifford.ConformalLieAlgebra55.v5_sq,
              mul_zero, zero_add]
    _ = 1 * v5 := by
      rw [InfoGeometry.Clifford.ConformalLieAlgebra55.u5_v5_add_v5_u5]
    _ = v5 := one_mul _

theorem J5_polarization_factorization :
    J5 = (u5 * v5 - v5 * u5) * (u5 + v5) := by
  calc
    J5 = u5 - v5 := rfl
    _ = u5 * v5 * u5 - v5 * u5 * v5 := by
      rw [u5_v5_u5, v5_u5_v5]
    _ = (u5 * v5 - v5 * u5) * (u5 + v5) := by
      rw [sub_mul, mul_add, mul_add]
      rw [mul_assoc u5 v5 v5, InfoGeometry.Clifford.ConformalLieAlgebra55.v5_sq,
        mul_zero]
      rw [mul_assoc v5 u5 u5, InfoGeometry.Clifford.ConformalLieAlgebra55.u5_sq,
        mul_zero]
      simp

theorem J5_reverse_factorization :
    (u5 + v5) * (u5 * v5 - v5 * u5) = -J5 := by
  rw [add_mul, mul_sub, mul_sub]
  rw [← mul_assoc u5 u5 v5, InfoGeometry.Clifford.ConformalLieAlgebra55.u5_sq,
    zero_mul]
  rw [← mul_assoc v5 v5 u5, InfoGeometry.Clifford.ConformalLieAlgebra55.v5_sq,
    zero_mul]
  rw [← mul_assoc u5 v5 u5]
  rw [← mul_assoc v5 u5 v5]
  rw [u5_v5_u5, v5_u5_v5]
  simp [J5]
  abel

lemma u4_v4_u4 :
    u4 * v4 * u4 = u4 := by
  calc
    u4 * v4 * u4
        = (u4 * v4 + v4 * u4) * u4 := by
            rw [add_mul]
            rw [mul_assoc v4 u4 u4, InfoGeometry.Clifford.ConformalLieAlgebra55.u4_sq,
              mul_zero, add_zero]
    _ = 1 * u4 := by
      rw [InfoGeometry.Clifford.ConformalLieAlgebra55.u4_v4_add_v4_u4]
    _ = u4 := one_mul _

lemma v4_u4_v4 :
    v4 * u4 * v4 = v4 := by
  calc
    v4 * u4 * v4
        = (u4 * v4 + v4 * u4) * v4 := by
            rw [add_mul]
            rw [mul_assoc u4 v4 v4, InfoGeometry.Clifford.ConformalLieAlgebra55.v4_sq,
              mul_zero, zero_add]
    _ = 1 * v4 := by
      rw [InfoGeometry.Clifford.ConformalLieAlgebra55.u4_v4_add_v4_u4]
    _ = v4 := one_mul _

theorem J4_polarization_factorization :
    J4 = (u4 * v4 - v4 * u4) * (u4 + v4) := by
  calc
    J4 = u4 - v4 := rfl
    _ = u4 * v4 * u4 - v4 * u4 * v4 := by
      rw [u4_v4_u4, v4_u4_v4]
    _ = (u4 * v4 - v4 * u4) * (u4 + v4) := by
      rw [sub_mul, mul_add, mul_add]
      rw [mul_assoc u4 v4 v4, InfoGeometry.Clifford.ConformalLieAlgebra55.v4_sq,
        mul_zero]
      rw [mul_assoc v4 u4 u4, InfoGeometry.Clifford.ConformalLieAlgebra55.u4_sq,
        mul_zero]
      simp

theorem J4_reverse_factorization :
    (u4 + v4) * (u4 * v4 - v4 * u4) = -J4 := by
  rw [add_mul, mul_sub, mul_sub]
  rw [← mul_assoc u4 u4 v4, InfoGeometry.Clifford.ConformalLieAlgebra55.u4_sq,
    zero_mul]
  rw [← mul_assoc v4 v4 u4, InfoGeometry.Clifford.ConformalLieAlgebra55.v4_sq,
    zero_mul]
  rw [← mul_assoc u4 v4 u4]
  rw [← mul_assoc v4 u4 v4]
  rw [u4_v4_u4, v4_u4_v4]
  simp [J4]
  abel

theorem gradeInvol_J5 :
    CliffordAlgebra.involute J5 = -J5 := by
  simp [J5, u5, v5,
    InfoGeometry.Clifford.ClNN.Quad,
    InfoGeometry.Clifford.ClNN.gammaHeadNullMinus,
    InfoGeometry.Clifford.ClNN.gammaHeadNullPlus]
  abel

theorem gradeInvol_J4 :
    CliffordAlgebra.involute J4 = -J4 := by
  simp [J4, u4, v4,
    InfoGeometry.Clifford.ClNN.Quad,
    InfoGeometry.Clifford.ClNN.gammaTail]
  abel

theorem gradeInvol_J :
    CliffordAlgebra.involute J = J := by
  rw [J, map_mul, gradeInvol_J5, gradeInvol_J4, neg_mul_neg]

/-! ### Matrix-level real spinor readbacks -/

noncomputable def spinorJ5 :
    InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  InfoGeometry.Clifford.SpinorRep.spinorRepresentation 5 J5

noncomputable def spinorJ4 :
    InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  InfoGeometry.Clifford.SpinorRep.spinorRepresentation 5 J4

noncomputable def spinorJ :
    InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  InfoGeometry.Clifford.SpinorRep.spinorRepresentation 5 J

theorem spinorJ5_sq : spinorJ5 * spinorJ5 = -(1 :
    InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
  rw [spinorJ5, ← map_mul, InfoGeometry.Clifford.ConformalLieAlgebra55.J5_sq]
  simp

theorem spinorJ4_sq : spinorJ4 * spinorJ4 = -(1 :
    InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
  rw [spinorJ4, ← map_mul, InfoGeometry.Clifford.ConformalLieAlgebra55.J4_sq]
  simp

theorem spinorJ_sq : spinorJ * spinorJ = -(1 :
    InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5) := by
  rw [spinorJ, ← map_mul, InfoGeometry.Clifford.ConformalLieAlgebra55.J_sq]
  simp

theorem jordanDet :
    ∀ X : InfoGeometry.Algebra.JordanCayleyInversionOsQ.Herm2x2OsQ,
      X.det = InfoGeometry.Physics.Pin55Formal.q55
        (InfoGeometry.Canonical.Herm2x2OsO55RationalBridge.toVec55Q X) := by
  intro X
  exact InfoGeometry.Canonical.Herm2x2OsO55RationalBridge.det_eq_q55_toVec55Q X

theorem jordanNullSwap :
    ∀ X : InfoGeometry.Algebra.JordanCayleyInversionOsQ.Herm2x2OsQ,
      InfoGeometry.Canonical.Herm2x2OsO55RationalBridge.toVec55Q
          (InfoGeometry.Canonical.Herm2x2OsO55RationalBridge.nullSwap X) =
        InfoGeometry.Canonical.Herm2x2OsO55RationalBridge.nullSwap55Vec
          (InfoGeometry.Canonical.Herm2x2OsO55RationalBridge.toVec55Q X) := by
  intro X
  exact InfoGeometry.Canonical.Herm2x2OsO55RationalBridge.toVec55Q_nullSwap X

end InfoGeometry.Canonical.Pin55CliffordBridge
