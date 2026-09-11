import InfoGeometry.Topology.CantorBoundaryCuntzLengthTwoSector
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Singular.DrazinGreen

noncomputable section

/-!
# Algebraic Drazin data for the concrete projected O₄ chiral sector

The concrete length-two Cantor owner already defines the grouped operators
`qPlusC`, `qMinusC`, the proper projection `P`, and the projected Dirac square.
This file adds only the missing ring-theoretic Drazin consequences.  It does
not claim Moore--Penrose equations: the concrete linear-map carrier has no
verified `StarRing`/Hilbert structure in this owner.
-/

namespace InfoGeometry.Canonical.CantorO4ChiralDrazinDefect

open InfoGeometry.Topology.CantorBoundaryCuntzLengthTwoSector
open InfoGeometry.Algebra.CuntzChiralSuperchargeRepresentation
open InfoGeometry.Singular.Drazin

theorem qPlusC_generalized_inverse :
    qPlusC * qMinusC * qPlusC = qPlusC := by
  change QPlus g * QMinus g * QPlus g = QPlus g
  rw [qplus_qminus_product g o11]
  change (gS0 * gT0) * (gS0 * gT1) = gS0 * gT1
  rw [mul_assoc, ← mul_assoc gT0, o00, one_mul]

theorem qMinusC_generalized_inverse :
    qMinusC * qPlusC * qMinusC = qMinusC := by
  change QMinus g * QPlus g * QMinus g = QMinus g
  rw [qminus_qplus_product g o00]
  change (gS1 * gT1) * (gS1 * gT0) = gS1 * gT0
  rw [mul_assoc, ← mul_assoc gT1, o11, one_mul]

theorem P_mul_qPlusC : P * qPlusC = qPlusC := by
  rw [← qC_anticommutator]
  calc
    (qPlusC * qMinusC + qMinusC * qPlusC) * qPlusC =
        qPlusC * qMinusC * qPlusC + qMinusC * (qPlusC * qPlusC) := by
          noncomm_ring
    _ = qPlusC := by rw [qPlusC_generalized_inverse, qPlusC_sq]; simp

theorem qPlusC_mul_P : qPlusC * P = qPlusC := by
  rw [← qC_anticommutator]
  calc
    qPlusC * (qPlusC * qMinusC + qMinusC * qPlusC) =
        (qPlusC * qPlusC) * qMinusC + qPlusC * qMinusC * qPlusC := by
          noncomm_ring
    _ = qPlusC := by rw [qPlusC_sq, qPlusC_generalized_inverse]; simp

theorem P_mul_qMinusC : P * qMinusC = qMinusC := by
  rw [← qC_anticommutator]
  calc
    (qPlusC * qMinusC + qMinusC * qPlusC) * qMinusC =
        qPlusC * (qMinusC * qMinusC) + qMinusC * qPlusC * qMinusC := by
          noncomm_ring
    _ = qMinusC := by rw [qMinusC_sq, qMinusC_generalized_inverse]; simp

theorem qMinusC_mul_P : qMinusC * P = qMinusC := by
  rw [← qC_anticommutator]
  calc
    qMinusC * (qPlusC * qMinusC + qMinusC * qPlusC) =
        qMinusC * qPlusC * qMinusC + (qMinusC * qMinusC) * qPlusC := by
          noncomm_ring
    _ = qMinusC := by rw [qMinusC_generalized_inverse, qMinusC_sq]; simp

theorem projectedDirac_mul_P :
    (qPlusC + qMinusC) * P = qPlusC + qMinusC := by
  rw [add_mul, qPlusC_mul_P, qMinusC_mul_P]

theorem P_mul_projectedDirac :
    P * (qPlusC + qMinusC) = qPlusC + qMinusC := by
  rw [mul_add, P_mul_qPlusC, P_mul_qMinusC]

theorem projectedDirac_mul_drazin_residue_projector :
    (qPlusC + qMinusC) * (1 - P) = 0 := by
  rw [mul_sub, mul_one, projectedDirac_mul_P]
  simp

theorem drazin_residue_projector_mul_projectedDirac :
    (1 - P) * (qPlusC + qMinusC) = 0 := by
  rw [sub_mul, one_mul, P_mul_projectedDirac]
  simp

theorem projectedDirac_drazin_one :
    IsDrazinInverse (qPlusC + qMinusC) (qPlusC + qMinusC) 1 := by
  refine IsDrazinInverse.mk ?_ rfl ?_
  · rw [show (qPlusC + qMinusC) * (qPlusC + qMinusC) = P by exact qC_dirac_square]
    exact P_mul_projectedDirac
  · rw [show (qPlusC + qMinusC) ^ 1 = qPlusC + qMinusC by simp]
    rw [show (qPlusC + qMinusC) ^ (1 + 1) = P by simpa [pow_two] using qC_dirac_square]
    exact P_mul_projectedDirac.symm

theorem projectedDirac_drazin_core_projector_eq_P :
    Drazin_Projector (qPlusC + qMinusC) (qPlusC + qMinusC) 1
        projectedDirac_drazin_one = P := by
  simp only [Drazin_Projector]
  exact qC_dirac_square

theorem projectedDirac_drazin_residue_projector_eq_complement :
    Drazin_ResidueProjector (qPlusC + qMinusC) (qPlusC + qMinusC) 1
        projectedDirac_drazin_one = 1 - P := by
  rw [Drazin_ResidueProjector, projectedDirac_drazin_core_projector_eq_P]

theorem qPlusC_drazin_zero :
    IsDrazinInverse qPlusC 0 2 := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · simp
  · simp
  · rw [show qPlusC ^ 2 = 0 by simpa [pow_two] using qPlusC_sq]
    simp

theorem qMinusC_drazin_zero :
    IsDrazinInverse qMinusC 0 2 := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · simp
  · simp
  · rw [show qMinusC ^ 2 = 0 by simpa [pow_two] using qMinusC_sq]
    simp

theorem qPlusC_drazin_core_projector_eq_zero :
    Drazin_Projector qPlusC 0 2 qPlusC_drazin_zero = 0 := by
  simp [Drazin_Projector]

theorem qMinusC_drazin_core_projector_eq_zero :
    Drazin_Projector qMinusC 0 2 qMinusC_drazin_zero = 0 := by
  simp [Drazin_Projector]

theorem qPlusC_drazin_residue_projector_eq_one :
    Drazin_ResidueProjector qPlusC 0 2 qPlusC_drazin_zero = 1 := by
  simp [Drazin_ResidueProjector, Drazin_Projector]

theorem qMinusC_drazin_residue_projector_eq_one :
    Drazin_ResidueProjector qMinusC 0 2 qMinusC_drazin_zero = 1 := by
  simp [Drazin_ResidueProjector, Drazin_Projector]

theorem projected_dirac_square_eq_P :
    projectedCantorDirac * projectedCantorDirac = P :=
  projectedCantorDirac_square

end InfoGeometry.Canonical.CantorO4ChiralDrazinDefect
