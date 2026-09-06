import proofs.HestenesHodgeParityBridge

/-!
# Hodge-dual boost and rotation bivectors

This owner fixes the orientation and proves the concrete Lorentzian Hodge
pair used by the loxodromic sector.
-/

noncomputable section
namespace HestenesHodgeBivector

open HestenesCl14
open HestenesCliffordCenter
open HestenesHodgeParityBridge

abbrev Algebra := Cl14

def boostBivector : Algebra := gamma 1 * gamma 0
def rotationBivector : Algebra := gamma 2 * gamma 3

private theorem gamma_comm_neg {i j : Fin 4} (hij : i ≠ j) :
    gamma j * gamma i = -(gamma i * gamma j) := by
  exact eq_neg_of_add_eq_zero_right (gamma_anticomm hij)

@[simp] theorem boostBivector_sq : boostBivector * boostBivector = 1 := by
  have h10 : gamma 0 * gamma 1 = -(gamma 1 * gamma 0) :=
    gamma_comm_neg (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide)
  simp only [boostBivector, mul_assoc]
  rw [show gamma 1 * (gamma 0 * (gamma 1 * gamma 0)) =
      gamma 1 * ((gamma 0 * gamma 1) * gamma 0) by simp [mul_assoc], h10]
  simp [mul_assoc]

@[simp] theorem rotationBivector_sq :
    rotationBivector * rotationBivector = -1 := by
  have h32 : gamma 3 * gamma 2 = -(gamma 2 * gamma 3) :=
    gamma_comm_neg (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  simp only [rotationBivector, mul_assoc]
  rw [show gamma 2 * (gamma 3 * (gamma 2 * gamma 3)) =
      gamma 2 * ((gamma 3 * gamma 2) * gamma 3) by simp [mul_assoc], h32]
  simp [mul_assoc]

theorem hodge_boost : hodge boostBivector = rotationBivector := by
  have h10 : gamma 1 * gamma 0 = -(gamma 0 * gamma 1) :=
    gamma_comm_neg (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
  simp only [hodge, boostBivector, rotationBivector,
    spacetimePseudoscalar_val]
  change CliffordAlgebra.reverse (gamma 1 * gamma 0) *
      (gamma 0 * gamma 1 * gamma 2 * gamma 3) = gamma 2 * gamma 3
  rw [CliffordAlgebra.reverse.map_mul]
  have hr0 : CliffordAlgebra.reverse (gamma 0) = gamma 0 := by simp [gamma]
  have hr1 : CliffordAlgebra.reverse (gamma 1) = gamma 1 := by simp [gamma]
  rw [hr0, hr1]
  calc
    (gamma 0 * gamma 1) * (gamma 0 * gamma 1 * gamma 2 * gamma 3) =
        gamma 0 * (gamma 1 * gamma 0) * gamma 1 * gamma 2 * gamma 3 := by
          simp [mul_assoc]
    _ = gamma 0 * (-(gamma 0 * gamma 1)) * gamma 1 * gamma 2 * gamma 3 := by
          rw [h10]
    _ = gamma 2 * gamma 3 := by
          noncomm_ring [gamma_zero_sq, gamma_one_sq]

theorem hodge_rotation : hodge rotationBivector = -boostBivector := by
  have h20 : gamma 2 * gamma 0 = -(gamma 0 * gamma 2) :=
    gamma_comm_neg (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  have h30 : gamma 3 * gamma 0 = -(gamma 0 * gamma 3) :=
    gamma_comm_neg (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have h21 : gamma 2 * gamma 1 = -(gamma 1 * gamma 2) :=
    gamma_comm_neg (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  have h31 : gamma 3 * gamma 1 = -(gamma 1 * gamma 3) :=
    gamma_comm_neg (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have h10 : gamma 0 * gamma 1 = -(gamma 1 * gamma 0) :=
    gamma_comm_neg (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide)
  have h321 : gamma 3 * gamma 2 * gamma 1 =
      gamma 1 * gamma 3 * gamma 2 := by
    calc
      gamma 3 * gamma 2 * gamma 1 = gamma 3 * (gamma 2 * gamma 1) := by
        simp [mul_assoc]
      _ = gamma 3 * (-(gamma 1 * gamma 2)) := by rw [h21]
      _ = -(gamma 3 * gamma 1) * gamma 2 := by noncomm_ring
      _ = -(-(gamma 1 * gamma 3)) * gamma 2 := by rw [h31]
      _ = gamma 1 * gamma 3 * gamma 2 := by noncomm_ring
  simp only [hodge, boostBivector, rotationBivector,
    spacetimePseudoscalar_val]
  change CliffordAlgebra.reverse (gamma 2 * gamma 3) *
      (gamma 0 * gamma 1 * gamma 2 * gamma 3) = -(gamma 1 * gamma 0)
  rw [CliffordAlgebra.reverse.map_mul]
  have hr2 : CliffordAlgebra.reverse (gamma 2) = gamma 2 := by simp [gamma]
  have hr3 : CliffordAlgebra.reverse (gamma 3) = gamma 3 := by simp [gamma]
  rw [hr2, hr3]
  calc
    (gamma 3 * gamma 2) * (gamma 0 * gamma 1 * gamma 2 * gamma 3) =
        gamma 3 * (gamma 2 * gamma 0) * gamma 1 * gamma 2 * gamma 3 := by
          simp [mul_assoc]
    _ = gamma 3 * (-(gamma 0 * gamma 2)) * gamma 1 * gamma 2 * gamma 3 := by
          rw [h20]
    _ = gamma 0 * gamma 3 * gamma 2 * gamma 1 * gamma 2 * gamma 3 := by
          rw [show gamma 3 * (-(gamma 0 * gamma 2)) =
            gamma 0 * gamma 3 * gamma 2 by
              calc
                gamma 3 * (-(gamma 0 * gamma 2)) =
                    -(gamma 3 * gamma 0) * gamma 2 := by noncomm_ring
                _ = -(-(gamma 0 * gamma 3)) * gamma 2 := by rw [h30]
                _ = gamma 0 * gamma 3 * gamma 2 := by noncomm_ring]
    _ = -(gamma 1 * gamma 0) := by
          rw [show gamma 0 * gamma 3 * gamma 2 * gamma 1 * gamma 2 * gamma 3 =
            gamma 0 * gamma 1 * gamma 3 * gamma 2 * gamma 2 * gamma 3 by
              noncomm_ring [h321]]
          noncomm_ring [gamma_two_sq, gamma_three_sq, h10]

theorem boost_rotation_commute :
    boostBivector * rotationBivector =
      rotationBivector * boostBivector := by
  have h20 : gamma 2 * gamma 1 = -(gamma 1 * gamma 2) :=
    gamma_comm_neg (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  have h30 : gamma 3 * gamma 1 = -(gamma 1 * gamma 3) :=
    gamma_comm_neg (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  have h02 : gamma 2 * gamma 0 = -(gamma 0 * gamma 2) :=
    gamma_comm_neg (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
  have h03 : gamma 3 * gamma 0 = -(gamma 0 * gamma 3) :=
    gamma_comm_neg (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  simp only [boostBivector, rotationBivector]
  calc
    (gamma 1 * gamma 0) * (gamma 2 * gamma 3) =
        gamma 1 * gamma 0 * gamma 2 * gamma 3 := by simp [mul_assoc]
    _ = gamma 2 * gamma 3 * gamma 1 * gamma 0 := by
      rw [show gamma 2 * gamma 3 * gamma 1 * gamma 0 =
          gamma 2 * (gamma 3 * gamma 1) * gamma 0 by simp [mul_assoc], h30]
      rw [show gamma 2 * -(gamma 1 * gamma 3) * gamma 0 =
          -(gamma 2 * gamma 1) * gamma 3 * gamma 0 by noncomm_ring, h20]
      rw [show -(-(gamma 1 * gamma 2)) * gamma 3 * gamma 0 =
          gamma 1 * gamma 2 * gamma 3 * gamma 0 by noncomm_ring]
      rw [show gamma 1 * gamma 2 * gamma 3 * gamma 0 =
          gamma 1 * gamma 2 * (gamma 3 * gamma 0) by simp [mul_assoc], h03]
      rw [show gamma 1 * gamma 2 * -(gamma 0 * gamma 3) =
          -gamma 1 * (gamma 2 * gamma 0) * gamma 3 by noncomm_ring, h02]
      noncomm_ring
    _ = (gamma 2 * gamma 3) * (gamma 1 * gamma 0) := by simp [mul_assoc]

theorem hodge_sq_boost : hodge (hodge boostBivector) = -boostBivector := by
  rw [hodge_boost, hodge_rotation]

theorem boost_hodge_packet :
    hodge boostBivector = rotationBivector ∧
    boostBivector * boostBivector = 1 ∧
    rotationBivector * rotationBivector = -1 ∧
    boostBivector * rotationBivector = rotationBivector * boostBivector ∧
    hodge (hodge boostBivector) = -boostBivector :=
  ⟨hodge_boost, boostBivector_sq, rotationBivector_sq,
    boost_rotation_commute, hodge_sq_boost⟩

end HestenesHodgeBivector
end noncomputable section
