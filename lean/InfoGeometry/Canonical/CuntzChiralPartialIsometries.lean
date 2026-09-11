import InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Singular.MoorePenrose
import InfoGeometry.Singular.Drazin
import InfoGeometry.Singular.DrazinGreen

noncomputable section

/-!
# Moore--Penrose packet for Cuntz chiral partial isometries

The Cuntz chiral source has two distinct projectors.  The range projector of
`QPlus` is `S1 * S1star`, while its source projector is `S2 * S2star`.
This file records the Penrose equations under the explicit adjoint-data
needed for the metric statements; no Hilbert-space structure is inferred
from the bare Cuntz relations.
-/

namespace InfoGeometry.Canonical.CuntzChiralPartialIsometries

open InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Singular.Drazin

variable {R : Type*} [Ring R] [StarRing R]

variable (g : CuntzO2Generators R)
variable (h11 : g.S1star * g.S1 = 1)
variable (h22 : g.S2star * g.S2 = 1)
variable (h12 : g.S1star * g.S2 = 0)
variable (h21 : g.S2star * g.S1 = 0)
variable (hs1 : star g.S1 = g.S1star)
variable (hs2 : star g.S2 = g.S2star)

@[simp] theorem qPlus_source_projector (h11 : g.S1star * g.S1 = 1) :
    QMinus g * QPlus g = g.S2 * g.S2star :=
  qminus_qplus_product g h11

@[simp] theorem qMinus_source_projector (h22 : g.S2star * g.S2 = 1) :
    QPlus g * QMinus g = g.S1 * g.S1star :=
  qplus_qminus_product g h22

theorem star_qPlus (hs1 : star g.S1 = g.S1star)
    (hs2 : star g.S2 = g.S2star) : star (QPlus g) = QMinus g := by
  have hs1' : star g.S1star = g.S1 := by rw [← hs1, star_star]
  have hs2' : star g.S2star = g.S2 := by rw [← hs2, star_star]
  simp [QPlus, QMinus, star_mul, hs1, hs2, hs1', hs2']

theorem star_qMinus (hs1 : star g.S1 = g.S1star)
    (hs2 : star g.S2 = g.S2star) : star (QMinus g) = QPlus g := by
  have hs1' : star g.S1star = g.S1 := by rw [← hs1, star_star]
  have hs2' : star g.S2star = g.S2 := by rw [← hs2, star_star]
  simp [QPlus, QMinus, star_mul, hs1, hs2, hs1', hs2']

theorem qPlus_moorePenroseInverse
    (h11 : g.S1star * g.S1 = 1) (h22 : g.S2star * g.S2 = 1)
    (hs1 : star g.S1 = g.S1star) (hs2 : star g.S2 = g.S2star) :
    IsMoorePenroseInverse (QPlus g) (QMinus g) := by
  refine IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · rw [qplus_qminus_product g h22]
    change (g.S1 * g.S1star) * (g.S1 * g.S2star) = g.S1 * g.S2star
    rw [mul_assoc, ← mul_assoc g.S1star, h11, one_mul]
  · rw [qminus_qplus_product g h11]
    change (g.S2 * g.S2star) * (g.S2 * g.S1star) = g.S2 * g.S1star
    rw [mul_assoc, ← mul_assoc g.S2star, h22, one_mul]
  · rw [qMinus_source_projector g h22]
    have hs1' : star g.S1star = g.S1 := by rw [← hs1, star_star]
    have hs2' : star g.S2star = g.S2 := by rw [← hs2, star_star]
    simp [QPlus, QMinus, star_mul, hs1, hs2, hs1', hs2']
  · rw [qPlus_source_projector g h11]
    have hs1' : star g.S1star = g.S1 := by rw [← hs1, star_star]
    have hs2' : star g.S2star = g.S2 := by rw [← hs2, star_star]
    simp [QPlus, QMinus, star_mul, hs1, hs2, hs1', hs2']

theorem qMinus_moorePenroseInverse
    (h11 : g.S1star * g.S1 = 1) (h22 : g.S2star * g.S2 = 1)
    (hs1 : star g.S1 = g.S1star) (hs2 : star g.S2 = g.S2star) :
    IsMoorePenroseInverse (QMinus g) (QPlus g) := by
  refine IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · rw [qminus_qplus_product g h11]
    change (g.S2 * g.S2star) * (g.S2 * g.S1star) = g.S2 * g.S1star
    rw [mul_assoc, ← mul_assoc g.S2star, h22, one_mul]
  · rw [qplus_qminus_product g h22]
    change (g.S1 * g.S1star) * (g.S1 * g.S2star) = g.S1 * g.S2star
    rw [mul_assoc, ← mul_assoc g.S1star, h11, one_mul]
  · rw [qPlus_source_projector g h11]
    have hs1' : star g.S1star = g.S1 := by rw [← hs1, star_star]
    have hs2' : star g.S2star = g.S2 := by rw [← hs2, star_star]
    simp [QPlus, QMinus, star_mul, hs1, hs2, hs1', hs2']
  · rw [qMinus_source_projector g h22]
    have hs1' : star g.S1star = g.S1 := by rw [← hs1, star_star]
    have hs2' : star g.S2star = g.S2 := by rw [← hs2, star_star]
    simp [QPlus, QMinus, star_mul, hs1, hs2, hs1', hs2']

def rangeProjector : R := QPlus g * QMinus g
def sourceProjector : R := QMinus g * QPlus g

theorem rangeProjector_eq (h22 : g.S2star * g.S2 = 1) :
    rangeProjector g = g.S1 * g.S1star := by
  exact qMinus_source_projector g h22

theorem sourceProjector_eq (h11 : g.S1star * g.S1 = 1) :
    sourceProjector g = g.S2 * g.S2star := by
  exact qPlus_source_projector g h11

theorem rangeProjector_idempotent
    (h11 : g.S1star * g.S1 = 1) (h22 : g.S2star * g.S2 = 1)
    (hs1 : star g.S1 = g.S1star) (hs2 : star g.S2 = g.S2star) :
    rangeProjector g * rangeProjector g = rangeProjector g := by
  exact MP_Projector_idempotent (qPlus_moorePenroseInverse g h11 h22 hs1 hs2)

theorem sourceProjector_idempotent
    (h11 : g.S1star * g.S1 = 1) (h22 : g.S2star * g.S2 = 1)
    (hs1 : star g.S1 = g.S1star) (hs2 : star g.S2 = g.S2star) :
    sourceProjector g * sourceProjector g = sourceProjector g := by
  exact MP_Projector_idempotent (qMinus_moorePenroseInverse g h11 h22 hs1 hs2)

theorem qPlus_drazin_zero (h21 : g.S2star * g.S1 = 0) :
    IsDrazinInverse (QPlus g) 0 2 := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · simp
  · simp
  · rw [show QPlus g ^ 2 = 0 by simpa [pow_two] using qplus_nilpotent g h21]
    simp

theorem qMinus_drazin_zero (h12 : g.S1star * g.S2 = 0) :
    IsDrazinInverse (QMinus g) 0 2 := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · simp
  · simp
  · rw [show QMinus g ^ 2 = 0 by simpa [pow_two] using qminus_nilpotent g h12]
    simp

theorem qPlus_drazin_core_projector_eq_zero (h21 : g.S2star * g.S1 = 0) :
    Drazin_Projector (QPlus g) 0 2 (qPlus_drazin_zero g h21) = 0 := by
  simp [Drazin_Projector]

theorem qMinus_drazin_core_projector_eq_zero (h12 : g.S1star * g.S2 = 0) :
    Drazin_Projector (QMinus g) 0 2 (qMinus_drazin_zero g h12) = 0 := by
  simp [Drazin_Projector]

theorem qPlus_drazin_residue_projector_eq_one (h21 : g.S2star * g.S1 = 0) :
    Drazin_ResidueProjector (QPlus g) 0 2 (qPlus_drazin_zero g h21) = 1 := by
  simp [Drazin_ResidueProjector, Drazin_Projector]

theorem qMinus_drazin_residue_projector_eq_one (h12 : g.S1star * g.S2 = 0) :
    Drazin_ResidueProjector (QMinus g) 0 2 (qMinus_drazin_zero g h12) = 1 := by
  simp [Drazin_ResidueProjector, Drazin_Projector]

end InfoGeometry.Canonical.CuntzChiralPartialIsometries
