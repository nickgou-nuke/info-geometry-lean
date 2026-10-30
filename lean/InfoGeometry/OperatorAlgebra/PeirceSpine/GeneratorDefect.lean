/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.GradedDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

/-! # Generator specializations of the graded defect identities

This is the later source packet reusing labels A49 and A50. It is distinct
from the transfer-discriminant packet. All equalities are in the ambient
associative ring; no Galois extension or Hilbert 90 assertion is made.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Core.IdempotentGraphGrassmannian
variable {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B)
include hP

theorem comm_P_add_phi :
    comm P (P + genPhi P A C) = genJ P A C := by
  peirce_nf hP

theorem comm_P_add_j :
    comm P (P + genJ P A C) = genPhi P A C := by
  peirce_nf hP

theorem comm_P_v_add_phi :
    comm P (genV P A C + genPhi P A C) = genJ P A C := by
  peirce_nf hP

theorem comm_grading_v_add_phi :
    comm (invS P) (genV P A C + genPhi P A C) = (2 : ℤ) • genJ P A C := by
  peirce_nf hP

theorem defect_transfer_neg_comm_square :
    idempotencyDefect (P + genPhi P A C) = -(comm P (P + genPhi P A C) * comm P (P + genPhi P A C)) := by
  simp only [idempotencyDefect]
  peirce_nf hP

theorem defect_transfer_j_neg_comm_square :
    idempotencyDefect (P + genJ P A C) = -(comm P (P + genJ P A C) * comm P (P + genJ P A C)) := by
  simp only [idempotencyDefect]
  peirce_nf hP

theorem defect_v_comm_square :
    idempotencyDefect (genV P A C) = genV P A C * genV P A C + comm P (genV P A C + genPhi P A C) * comm P (genV P A C + genPhi P A C) := by
  simp only [idempotencyDefect]
  peirce_nf hP

theorem defect_v_parity_product :
    idempotencyDefect (genV P A C) = (genV P A C + genPhi P A C) * parityConj P (genV P A C + genPhi P A C) := by
  simp only [idempotencyDefect, parityConj]
  peirce_nf hP

theorem defect_v_add_phi_even :
    evenGrade P (idempotencyDefect (genV P A C + genPhi P A C)) = idempotencyDefect (genV P A C) + genV P A C := by
  simp only [idempotencyDefect]
  peirce_nf hP

theorem defect_v_add_phi_odd :
    oddGrade P (idempotencyDefect (genV P A C + genPhi P A C)) = ((2 : ℤ) • genV P A C - 1) * genPhi P A C := by
  simp only [idempotencyDefect]
  peirce_nf hP

theorem defect_deriv_sig_sub_j :
    derivSqSig P A C (genPhi P A C) - derivSqJ P A C (genPhi P A C) = -((4 : ℤ) • (idempotencyDefect (genV P A C) * genPhi P A C)) := by
  simp only [idempotencyDefect, derivSqSig, derivSqJ]
  peirce_nf hP

theorem defect_deriv_sig_sub_phi :
    derivSqSig P A C (genJ P A C) - derivSqPhi P A C (genJ P A C) = -((4 : ℤ) • (idempotencyDefect (genV P A C) * genJ P A C)) := by
  simp only [idempotencyDefect, derivSqSig, derivSqPhi]
  peirce_nf hP

/-- The mismatch formula can be read directly from the second defect iterate
of the Peirce transfer element `P + Φ`; its first iterate is `V`. -/
theorem defect_deriv_sig_sub_j_transfer_iterate :
    derivSqSig P A C (genPhi P A C) - derivSqJ P A C (genPhi P A C) =
      -((4 : ℤ) •
        (idempotencyDefect (idempotencyDefect (P + genPhi P A C)) *
          genPhi P A C)) := by
  have hδ : idempotencyDefect (P + genPhi P A C) = genV P A C := by
    simpa [peirceTransfer] using (peirceTransfer_defect_and_vieta hP A C).1
  rw [hδ]
  exact defect_deriv_sig_sub_j hP A C

/-- The raw character projector on `J` is likewise expressed using the
second defect iterate of `P + Φ`. -/
theorem defect_proj_phi_j_transfer_iterate :
    projPhi P A C (genJ P A C) =
      (4 : ℤ) •
        (idempotencyDefect (idempotencyDefect (P + genPhi P A C)) *
          genJ P A C) := by
  have hδ : idempotencyDefect (P + genPhi P A C) = genV P A C := by
    simpa [peirceTransfer] using (peirceTransfer_defect_and_vieta hP A C).1
  have hProj := archetype_A11_klein_hadamard_character_selection hP A C
  rcases hProj with ⟨_, _, _, _, _, _, _, _, _, _, hProj, _, _, _⟩
  rw [hδ]
  simp only [idempotencyDefect]
  rw [hProj]
  simp only [sub_mul]

theorem transfer_parity_product_corrected :
    (P + genPhi P A C) * parityConj P (P + genPhi P A C) = P - genV P A C - genJ P A C := by
  simp only [parityConj]
  peirce_nf hP

theorem sigma_phi_square :
    (genSig P A C + genPhi P A C) * (genSig P A C + genPhi P A C) = genV P A C * genV P A C + genV P A C := by
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
