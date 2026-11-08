import InfoGeometry.Clifford.ConformalGeneratorLemmas55
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.ConformalLieAlgebra55Dilation
import InfoGeometry.Clifford.SpinorRep
import InfoGeometry.Canonical.Herm2x2OsO55RationalBridge

namespace InfoGeometry.Canonical.Pin55CliffordBridge

open InfoGeometry.Clifford.ConformalLift55
open InfoGeometry.Clifford.ConformalLieAlgebra55

def PolarizationReadback55 : Prop :=
  (u5 * u5 = 0 ∧ v5 * v5 = 0 ∧ u5 * v5 + v5 * u5 = 1) ∧
    (u4 * u4 = 0 ∧ v4 * v4 = 0 ∧ u4 * v4 + v4 * u4 = 1) ∧
    J5 * J5 = -1 ∧
    J4 * J4 = -1 ∧
    J * J = -1 ∧
    D * u5 - u5 * D = u5 ∧
    D * v5 - v5 * D = -v5 ∧
    D * u4 - u4 * D = u4 ∧
    D * v4 - v4 * D = -v4

namespace PolarizationReadback55

variable (h : PolarizationReadback55)

theorem null5 (h : PolarizationReadback55) : u5 * u5 = 0 ∧ v5 * v5 = 0 ∧ u5 * v5 + v5 * u5 = 1 := h.1
theorem null4 (h : PolarizationReadback55) : u4 * u4 = 0 ∧ v4 * v4 = 0 ∧ u4 * v4 + v4 * u4 = 1 := h.2.1
theorem phase5 (h : PolarizationReadback55) : J5 * J5 = -1 := h.2.2.1
theorem phase4 (h : PolarizationReadback55) : J4 * J4 = -1 := h.2.2.2.1
theorem combinedPhase (h : PolarizationReadback55) : J * J = -1 := h.2.2.2.2.1
theorem dilationPlus5 (h : PolarizationReadback55) : D * u5 - u5 * D = u5 := h.2.2.2.2.2.1
theorem dilationMinus5 (h : PolarizationReadback55) : D * v5 - v5 * D = -v5 := h.2.2.2.2.2.2.1
theorem dilationPlus4 (h : PolarizationReadback55) : D * u4 - u4 * D = u4 := h.2.2.2.2.2.2.2.1
theorem dilationMinus4 (h : PolarizationReadback55) : D * v4 - v4 * D = -v4 := h.2.2.2.2.2.2.2.2

end PolarizationReadback55

theorem polarizationReadback55Installed :
    PolarizationReadback55 := by
  exact ⟨⟨InfoGeometry.Clifford.ConformalLieAlgebra55.u5_sq,
      InfoGeometry.Clifford.ConformalLieAlgebra55.v5_sq,
      InfoGeometry.Clifford.ConformalLieAlgebra55.u5_v5_add_v5_u5⟩,
    ⟨InfoGeometry.Clifford.ConformalLieAlgebra55.u4_sq,
      InfoGeometry.Clifford.ConformalLieAlgebra55.v4_sq,
      InfoGeometry.Clifford.ConformalLieAlgebra55.u4_v4_add_v4_u4⟩,
    InfoGeometry.Clifford.ConformalLieAlgebra55.J5_sq,
    InfoGeometry.Clifford.ConformalLieAlgebra55.J4_sq,
    InfoGeometry.Clifford.ConformalLieAlgebra55.J_sq,
    InfoGeometry.Clifford.ConformalLieAlgebra55.adD_u5,
    InfoGeometry.Clifford.ConformalLieAlgebra55Dilation.adD_v5,
    InfoGeometry.Clifford.ConformalLieAlgebra55.adD_u4,
    InfoGeometry.Clifford.ConformalLieAlgebra55Dilation.adD_v4⟩

theorem two_smul_D5 :
    (2 : ℝ) • D5 = u5 * v5 - v5 * u5 := by
  simp [D5, smul_smul]

theorem two_smul_D4 :
    (2 : ℝ) • D4 = u4 * v4 - v4 * u4 := by
  simp [D4, smul_smul]

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

theorem polarization : PolarizationReadback55 :=
  polarizationReadback55Installed

theorem jordanCliffordPolarizationEvidence55Installed :
  (∀ X : InfoGeometry.Algebra.JordanCayleyInversionOsQ.Herm2x2OsQ,
      X.det = InfoGeometry.Physics.Pin55Formal.q55
        (InfoGeometry.Canonical.Herm2x2OsO55RationalBridge.toVec55Q X)) ∧
    (∀ X : InfoGeometry.Algebra.JordanCayleyInversionOsQ.Herm2x2OsQ,
      InfoGeometry.Canonical.Herm2x2OsO55RationalBridge.toVec55Q
          (InfoGeometry.Canonical.Herm2x2OsO55RationalBridge.nullSwap X) =
        InfoGeometry.Canonical.Herm2x2OsO55RationalBridge.nullSwap55Vec
          (InfoGeometry.Canonical.Herm2x2OsO55RationalBridge.toVec55Q X)) ∧
    PolarizationReadback55 := by
  exact ⟨jordanDet, jordanNullSwap, polarization⟩

end InfoGeometry.Canonical.Pin55CliffordBridge
