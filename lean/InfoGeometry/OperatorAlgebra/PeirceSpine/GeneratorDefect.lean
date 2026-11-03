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

/-- The second defect of the Peirce transfer `P + Φ` is the ordinary defect
of its first iterate `V`, namely `V² - V`. -/
theorem defect_transfer_second_iterate :
    idempotencyDefect (idempotencyDefect (P + genPhi P A C)) =
      genV P A C * genV P A C - genV P A C := by
  have hδ : idempotencyDefect (P + genPhi P A C) = genV P A C := by
    simpa [peirceTransfer] using (peirceTransfer_defect_and_vieta hP A C).1
  rw [hδ]
  rfl

/-- Left multiplication of the upper Peirce cone by the polynomial `V - 1`
changes its anticommutator with the opposite cone to the idempotency defect
of `V`. No inverse or centrality in the ambient ring is asserted; the proof
uses only Peirce corner relations. -/
theorem omega_polynomial_vielbein_defect (A C : B) :
    anticomm ((genV P A C - 1) * conePlus P A) (coneMinus P C) =
      genV P A C * genV P A C - genV P A C := by
  peirce_nf hP

/-- The same dressing sends the oriented return to the grading times the
metric defect. -/
theorem omega_polynomial_vielbein_commutator (A C : B) :
    comm ((genV P A C - 1) * conePlus P A) (coneMinus P C) =
      invS P * (genV P A C * genV P A C - genV P A C) := by
  peirce_nf hP

/-- The Omega dressing remains in the upper Peirce corner, hence remains
square-zero. -/
theorem omega_polynomial_vielbein_square_zero (A C : B) :
    ((genV P A C - 1) * conePlus P A) *
        ((genV P A C - 1) * conePlus P A) = 0 := by
  peirce_nf hP

/-- The Newton polynomial `3V - 2V²`, applied to the upper cone, produces
the polynomial metric `3V² - 2V³` against the lower cone. -/
theorem newton_polynomial_vielbein_metric (A C : B) :
    anticomm (((3 : ℤ) • genV P A C -
      (2 : ℤ) • (genV P A C * genV P A C)) * conePlus P A)
      (coneMinus P C) =
      (3 : ℤ) • (genV P A C * genV P A C) -
        (2 : ℤ) • (genV P A C * genV P A C * genV P A C) := by
  peirce_nf hP

/-- On the defect-one locus, the `V - 1` scaling normalizes the dressed
anticommutator to one. This is the algebraic Weyl-gauge specialization; the
shell condition is explicit, and no geometric gauge action or shell existence
is claimed. -/
theorem omega_polynomial_vielbein_unit_shell (A C : B)
    (hSeed : genV P A C * genV P A C - genV P A C = 1) :
    anticomm ((genV P A C - 1) * conePlus P A) (coneMinus P C) = 1 := by
  rw [omega_polynomial_vielbein_defect hP A C, hSeed]

/-- A common operator-valued scale commuting with the two Peirce cones
rescales their ordered upper-lower product quadratically. -/
theorem peirce_scale_upper_lower (r : B)
    (hPlus : r * conePlus P A = conePlus P A * r) :
    (r * conePlus P A) * (r * coneMinus P C) =
      (r * r) * (conePlus P A * coneMinus P C) := by
  calc
    (r * conePlus P A) * (r * coneMinus P C) =
        r * (conePlus P A * r) * coneMinus P C := by simp only [mul_assoc]
    _ = r * (r * conePlus P A) * coneMinus P C := by rw [hPlus]
    _ = (r * r) * (conePlus P A * coneMinus P C) := by simp only [mul_assoc]

/-- The reverse ordered product obeys the same scale law. -/
theorem peirce_scale_lower_upper (r : B)
    (hMinus : r * coneMinus P C = coneMinus P C * r) :
    (r * coneMinus P C) * (r * conePlus P A) =
      (r * r) * (coneMinus P C * conePlus P A) := by
  calc
    (r * coneMinus P C) * (r * conePlus P A) =
        r * (coneMinus P C * r) * conePlus P A := by simp only [mul_assoc]
    _ = r * (r * coneMinus P C) * conePlus P A := by rw [hMinus]
    _ = (r * r) * (coneMinus P C * conePlus P A) := by simp only [mul_assoc]

/-- The operator-valued Weyl scaling law for the symmetric Peirce metric.
No commutativity of the ambient ring is assumed: only the scale's action on
the two cone generators is specified. -/
theorem peirce_weyl_scale_metric (r : B)
    (hPlus : r * conePlus P A = conePlus P A * r)
    (hMinus : r * coneMinus P C = coneMinus P C * r) :
    anticomm (r * conePlus P A) (r * coneMinus P C) =
      (r * r) * genV P A C := by
  change (r * conePlus P A) * (r * coneMinus P C) +
      (r * coneMinus P C) * (r * conePlus P A) =
    (r * r) * (conePlus P A * coneMinus P C + coneMinus P C * conePlus P A)
  rw [peirce_scale_upper_lower hP A C r hPlus,
      peirce_scale_lower_upper hP A C r hMinus, ← mul_add]

/-- The oriented Peirce curvature has the same quadratic Weyl weight as the
symmetric metric. -/
theorem peirce_weyl_scale_curvature (r : B)
    (hPlus : r * conePlus P A = conePlus P A * r)
    (hMinus : r * coneMinus P C = coneMinus P C * r) :
    comm (r * conePlus P A) (r * coneMinus P C) =
      (r * r) * genSig P A C := by
  change (r * conePlus P A) * (r * coneMinus P C) -
      (r * coneMinus P C) * (r * conePlus P A) =
    (r * r) * (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A)
  rw [peirce_scale_upper_lower hP A C r hPlus,
      peirce_scale_lower_upper hP A C r hMinus, ← mul_sub]

/-- If the squared scale sends the metric to the identity, the rescaled
Peirce pair has unit anticommutator. This is the algebraic Weyl-gauge
normalization law; invertibility is not needed for this implication. -/
theorem peirce_weyl_scale_unit_metric (r : B)
    (hPlus : r * conePlus P A = conePlus P A * r)
    (hMinus : r * coneMinus P C = coneMinus P C * r)
    (hUnit : (r * r) * genV P A C = 1) :
    anticomm (r * conePlus P A) (r * coneMinus P C) = 1 := by
  rw [peirce_weyl_scale_metric hP A C r hPlus hMinus, hUnit]

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

/-- The idempotency defect packages the polarization, odd perturbation, and
vertical grade identities of the Peirce tetraktys. The statements are kept
operator-valued and ordered; no division by two or scalar model is used. -/
theorem archetype_A55_idempotency_defect_grade_generator (X Y : B) :
    idempotencyDefect (X + Y) - idempotencyDefect X - idempotencyDefect Y =
      anticomm X Y ∧
    idempotencyDefect (P + X) - idempotencyDefect X = anticomm P X ∧
    idempotencyDefect (genPhi P A C) -
      idempotencyDefect (conePlus P A) - idempotencyDefect (coneMinus P C) =
      genV P A C ∧
    idempotencyDefect (P + conePlus P A) = 0 ∧
    idempotencyDefect (P + coneMinus P C) = 0 ∧
    idempotencyDefect (P + genPhi P A C) = genV P A C ∧
    idempotencyDefect (P + genJ P A C) = -genV P A C ∧
    idempotencyDefect (P + comm P A) = comm P A * comm P A ∧
    idempotencyDefect (P + oddGrade P A) = oddGrade P A * oddGrade P A ∧
    idempotencyDefect (-genPhi P A C) + idempotencyDefect (genPhi P A C) =
      (2 : ℤ) • genV P A C ∧
    idempotencyDefect (-genPhi P A C) - idempotencyDefect (genPhi P A C) =
      (2 : ℤ) • genPhi P A C ∧
    idempotencyDefect (-genJ P A C) + idempotencyDefect (genJ P A C) =
      -((2 : ℤ) • genV P A C) ∧
    idempotencyDefect (-genJ P A C) - idempotencyDefect (genJ P A C) =
      (2 : ℤ) • genJ P A C ∧
    derivSqSig P A C (genPhi P A C) - derivSqJ P A C (genPhi P A C) =
      -((4 : ℤ) •
        (idempotencyDefect (idempotencyDefect (P + genPhi P A C)) *
          genPhi P A C)) ∧
    projPhi P A C (genJ P A C) =
      (4 : ℤ) •
        (idempotencyDefect (idempotencyDefect (P + genPhi P A C)) *
          genJ P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    defect_deriv_sig_sub_j_transfer_iterate hP A C,
    defect_proj_phi_j_transfer_iterate hP A C⟩
  · simpa [anticomm] using idempotencyDefect_add_polarization X Y
  ·
    have hδP : idempotencyDefect P = 0 := by
      simp [idempotencyDefect, hP]
    have hPol := idempotencyDefect_add_polarization P X
    rw [hδP] at hPol
    simpa [anticomm] using hPol
  · simp only [idempotencyDefect]
    peirce_nf hP
  · simp only [idempotencyDefect]
    peirce_nf hP
  · simp only [idempotencyDefect]
    peirce_nf hP
  · simp only [idempotencyDefect]
    peirce_nf hP
  · simp only [idempotencyDefect]
    peirce_nf hP
  · simp only [idempotencyDefect]
    peirce_nf hP
  · simp only [idempotencyDefect]
    peirce_nf hP
  · simp only [idempotencyDefect]
    peirce_nf hP
  · simp only [idempotencyDefect]
    peirce_nf hP
  · simp only [idempotencyDefect]
    peirce_nf hP
  · simp only [idempotencyDefect]
    peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
