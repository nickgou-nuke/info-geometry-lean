import InfoGeometry.OperatorAlgebra.PeirceSpine.GradingPerturbation
import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferDefect

/-!
# Transfer defects and grading commutator identities

Dependency order: Peirce corner relations → generator multiplication →
grading perturbation and transfer defect → the identities below.

All statements hold in the ambient associative ring. The double-commutator
coefficients are ring elements acting by left multiplication, not scalar
eigenvalues. No linear independence, eigenbasis, positivity, spectral gap,
or preservation of cohomology is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/-- Completing the square retains the factor four in every characteristic. -/
theorem square_completion_idempotencyDefect (X : B) :
    ((2 : ℤ) • X - 1) * ((2 : ℤ) • X - 1) =
      1 + (4 : ℤ) • idempotencyDefect X := by
  simp only [idempotencyDefect, two_zsmul]
  noncomm_ring

variable {P : B} (hP : P * P = P) (A C : B)
include hP

theorem transfer_defect_eq_grading_square_sub_one :
    idempotencyDefect (peirceTransfer P A C) =
      (invS P + genPhi P A C) * (invS P + genPhi P A C) - 1 := by
  rw [(peirceTransfer_defect_and_vieta hP A C).1, grading_add_phi_sq hP]
  simp [zetaPlusFactor]

theorem transfer_j_defect_eq_grading_square_sub_one :
    idempotencyDefect (peirceTransferJ P A C) =
      (invS P + genJ P A C) * (invS P + genJ P A C) - 1 := by
  rw [(peirceTransfer_defect_and_vieta hP A C).2.2.1, grading_add_j_sq hP]
  simp [zetaFactor]

omit hP in
theorem transfer_discriminant_eq :
    (2 : ℤ) • peirceTransfer P A C - 1 = invS P + (2 : ℤ) • genPhi P A C := by
  simp only [peirceTransfer, invS, two_zsmul]
  abel

theorem transfer_discriminant_square :
    ((2 : ℤ) • peirceTransfer P A C - 1) *
      ((2 : ℤ) • peirceTransfer P A C - 1) = 1 + (4 : ℤ) • genV P A C := by
  rw [square_completion_idempotencyDefect, (peirceTransfer_defect_and_vieta hP A C).1]

theorem transfer_j_discriminant_square :
    ((2 : ℤ) • peirceTransferJ P A C - 1) *
      ((2 : ℤ) • peirceTransferJ P A C - 1) = 1 - (4 : ℤ) • genV P A C := by
  rw [square_completion_idempotencyDefect,
    (peirceTransfer_defect_and_vieta hP A C).2.2.1]
  simp [sub_eq_add_neg]

theorem grading_phi_product_v :
    (invS P + genPhi P A C) * genV P A C =
      genV P A C * genPhi P A C + genSig P A C := by
  peirce_nf hP

theorem grading_phi_comm_product_v :
    comm (invS P + genPhi P A C)
      (genV P A C * genPhi P A C + genSig P A C) = 0 := by
  peirce_nf hP

theorem grading_phi_comm_phi_sub_sig :
    comm (invS P + genPhi P A C) (genPhi P A C - genSig P A C) =
      (2 : ℤ) • ((1 + genV P A C) * genJ P A C) := by
  peirce_nf hP

theorem grading_phi_double_comm_j :
    comm (invS P + genPhi P A C) (comm (invS P + genPhi P A C) (genJ P A C)) =
      (4 : ℤ) • ((1 + genV P A C) * genJ P A C) := by
  peirce_nf hP

theorem grading_phi_double_comm_phi_sub_sig :
    comm (invS P + genPhi P A C)
      (comm (invS P + genPhi P A C) (genPhi P A C - genSig P A C)) =
      (4 : ℤ) • ((1 + genV P A C) * (genPhi P A C - genSig P A C)) := by
  peirce_nf hP

theorem grading_j_double_comm_phi :
    comm (invS P + genJ P A C) (comm (invS P + genJ P A C) (genPhi P A C)) =
      (4 : ℤ) • ((1 - genV P A C) * genPhi P A C) := by
  peirce_nf hP

/-- Even when `V = 0`, the sandwich retains the odd contribution `2Φ`.
This is the exact criterion for the proposed unchanged-grading conclusion. -/
theorem grading_phi_sandwich_eq_grading_iff (hV : genV P A C = 0) :
    (invS P + genPhi P A C) * invS P * (invS P + genPhi P A C) = invS P ↔
      (2 : ℤ) • genPhi P A C = 0 := by
  rw [grading_phi_sandwich hP, zetaFactor, hV, sub_zero, one_mul, add_eq_left]

end InfoGeometry.OperatorAlgebra.PeirceSpine
