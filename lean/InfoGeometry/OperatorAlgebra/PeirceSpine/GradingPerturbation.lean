import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors

/-!
# Polynomial identities for an odd perturbation of a Peirce grading

The carrier is an arbitrary associative ring, including full matrix rings.
These are square, sandwich and commutator identities; no inverse or analytic
interpretation is assumed. The vocabulary and normal form belong to `Basic`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B)
include hP

theorem grading_add_phi_sq :
    (invS P + genPhi P A C) * (invS P + genPhi P A C) = zetaPlusFactor P A C := by
  simp only [zetaPlusFactor]
  peirce_nf hP

theorem grading_sub_phi_sq :
    (invS P - genPhi P A C) * (invS P - genPhi P A C) = zetaPlusFactor P A C := by
  simp only [zetaPlusFactor]
  peirce_nf hP

theorem grading_add_j_sq :
    (invS P + genJ P A C) * (invS P + genJ P A C) = zetaFactor P A C := by
  simp only [zetaFactor]
  peirce_nf hP

theorem grading_sub_j_sq :
    (invS P - genJ P A C) * (invS P - genJ P A C) = zetaFactor P A C := by
  simp only [zetaFactor]
  peirce_nf hP

theorem grading_phi_square_factorization :
    (invS P + genPhi P A C) * (invS P + genPhi P A C) =
      (1 + qgtPlus P A C) * (1 + qgtMinus P A C) :=
  (grading_add_phi_sq hP A C).trans (chiralEuler_factorizations hP A C).2.1.symm

theorem grading_j_square_factorization :
    (invS P + genJ P A C) * (invS P + genJ P A C) =
      (1 - qgtPlus P A C) * (1 - qgtMinus P A C) :=
  (grading_add_j_sq hP A C).trans (chiralEuler_factorizations hP A C).1.symm

theorem grading_phi_opposite_product :
    (invS P + genPhi P A C) * (invS P - genPhi P A C) =
      zetaFactor P A C - (2 : ℤ) • genJ P A C := by
  simp only [zetaFactor]
  peirce_nf hP

theorem grading_phi_opposite_anticomm :
    anticomm (invS P + genPhi P A C) (invS P - genPhi P A C) =
      (2 : ℤ) • zetaFactor P A C := by
  simp only [zetaFactor]
  peirce_nf hP

theorem grading_j_opposite_anticomm :
    anticomm (invS P + genJ P A C) (invS P - genJ P A C) =
      (2 : ℤ) • zetaPlusFactor P A C := by
  simp only [zetaPlusFactor]
  peirce_nf hP

theorem grading_perturbation_square_product :
    ((invS P + genPhi P A C) * (invS P + genPhi P A C)) *
      ((invS P + genJ P A C) * (invS P + genJ P A C)) =
      1 - genV P A C * genV P A C := by
  rw [grading_add_phi_sq hP, grading_add_j_sq hP]
  simp only [zetaPlusFactor, zetaFactor]
  noncomm_ring

theorem grading_phi_sandwich :
    (invS P + genPhi P A C) * invS P * (invS P + genPhi P A C) =
      zetaFactor P A C * invS P + (2 : ℤ) • genPhi P A C := by
  simp only [zetaFactor]
  peirce_nf hP

theorem grading_j_sandwich :
    (invS P + genJ P A C) * invS P * (invS P + genJ P A C) =
      zetaPlusFactor P A C * invS P + (2 : ℤ) • genJ P A C := by
  simp only [zetaPlusFactor]
  peirce_nf hP

theorem grading_phi_comm_v : comm (invS P + genPhi P A C) (genV P A C) = 0 := by
  peirce_nf hP

theorem grading_j_comm_v : comm (invS P + genJ P A C) (genV P A C) = 0 := by
  peirce_nf hP

theorem grading_phi_comm_phi :
    comm (invS P + genPhi P A C) (genPhi P A C) = (2 : ℤ) • genJ P A C := by
  peirce_nf hP

theorem grading_phi_comm_j :
    comm (invS P + genPhi P A C) (genJ P A C) =
      (2 : ℤ) • (genPhi P A C - genSig P A C) := by
  peirce_nf hP

theorem grading_phi_comm_sig :
    comm (invS P + genPhi P A C) (genSig P A C) =
      -((2 : ℤ) • (genV P A C * genJ P A C)) := by
  peirce_nf hP

theorem grading_phi_double_comm_phi :
    comm (invS P + genPhi P A C) (comm (invS P + genPhi P A C) (genPhi P A C)) =
      (4 : ℤ) • (genPhi P A C - genSig P A C) := by
  peirce_nf hP

theorem grading_phi_double_comm_grading :
    comm (invS P + genPhi P A C) (comm (invS P + genPhi P A C) (invS P)) =
      (4 : ℤ) • (genV P A C * invS P - genPhi P A C) := by
  peirce_nf hP

/-- Exact defect of the proposed unchanged-grading sandwich. -/
theorem grading_phi_sandwich_defect :
    (invS P + genPhi P A C) * invS P * (invS P + genPhi P A C) - invS P =
      -(genV P A C * invS P) + (2 : ℤ) • genPhi P A C := by
  rw [grading_phi_sandwich hP]
  simp only [zetaFactor, sub_mul, one_mul]
  abel

/-- The even part of the defect is the grading-weighted quadratic term. -/
theorem grading_phi_sandwich_defect_even :
    evenGrade P ((invS P + genPhi P A C) * invS P *
      (invS P + genPhi P A C) - invS P) = -(genV P A C * invS P) := by
  rw [grading_phi_sandwich_defect hP]
  simp only [two_zsmul]
  peirce_nf hP

/-- The odd part is precisely twice the off-diagonal perturbation. -/
theorem grading_phi_sandwich_defect_odd :
    oddGrade P ((invS P + genPhi P A C) * invS P *
      (invS P + genPhi P A C) - invS P) = (2 : ℤ) • genPhi P A C := by
  rw [grading_phi_sandwich_defect hP]
  simp only [two_zsmul]
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
