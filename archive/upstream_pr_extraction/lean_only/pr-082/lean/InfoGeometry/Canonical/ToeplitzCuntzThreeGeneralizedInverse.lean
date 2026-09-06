import InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge
import InfoGeometry.Singular.DrazinGreen
import InfoGeometry.Singular.MoorePenrose

noncomputable section

/-!
# Generalized inverse of the cyclic Toeplitz--Cuntz supercharge

The vacuum defect `P₀` is retained explicitly.  For the cyclic charge `Q`,
the active projection is `H = 1 - P₀`; both the Drazin and Moore--Penrose
witnesses are the concrete element `Q²`.  This is a statement about the
associative Toeplitz--Cuntz envelope and does not identify `P₀` with an
associator.
-/

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeGeneralizedInverse

open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge
open InfoGeometry.Singular.Drazin
open InfoGeometry.Singular.MoorePenrose

variable {A : Type*} [Ring A] [StarRing A]
variable (g : ToeplitzCuntzThreeGenerators A)

local notation "Q" => cyclicSupercharge g
local notation "H" => g.susyHamiltonian

lemma q_mul_h : Q * H = Q := by
  rw [susyHamiltonian_eq_one_sub_defect g, mul_sub, mul_one,
    cyclicSupercharge_defect_annihilation_right g, sub_zero]

lemma h_mul_q : H * Q = Q := by
  rw [susyHamiltonian_eq_one_sub_defect g, sub_mul, one_mul,
    cyclicSupercharge_defect_annihilation_left g, sub_zero]

lemma q_pow_three : Q ^ 3 = H := by
  simpa [pow_succ, pow_two, mul_assoc] using
    (cyclicSupercharge_cube_eq_hamiltonian g)

lemma q_pow_four : Q ^ 4 = Q := by
  calc
    Q ^ 4 = Q ^ 3 * Q := by simp [pow_succ]
    _ = H * Q := by rw [q_pow_three g]
    _ = Q := h_mul_q g

lemma q_pow_five : Q ^ 5 = Q ^ 2 := by
  calc
    Q ^ 5 = Q ^ 4 * Q := by simp [pow_succ]
    _ = Q * Q := by rw [q_pow_four g]
    _ = Q ^ 2 := by simp [pow_two]

theorem cyclicSupercharge_drazin_inverse_eq_square :
    IsDrazinInverse Q (Q ^ 2) 1 := by
  refine IsDrazinInverse.mk ?_ ?_ ?_
  · calc
      Q ^ 2 * Q * Q ^ 2 = Q ^ 5 := by simp [pow_succ, pow_two, mul_assoc]
      _ = Q ^ 2 := q_pow_five g
  · simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
  · calc
      Q ^ 1 = Q := by simp
      _ = Q ^ 4 := (q_pow_four g).symm
      _ = Q ^ (1 + 1) * Q ^ 2 := by simp [pow_succ, pow_two, mul_assoc]

theorem cyclicSupercharge_drazin_inverse_unique
    {D : A} (hD : IsDrazinInverse Q D 1) : D = Q ^ 2 := by
  exact Drazin_unique hD
    (cyclicSupercharge_drazin_inverse_eq_square g)

lemma star_q_pow_two : star (Q ^ 2) = Q := by
  calc
    star (Q ^ 2) = star Q * star Q := by
      rw [show Q ^ 2 = Q * Q by simp [pow_two], star_mul]
    _ = Q ^ 2 * Q ^ 2 := by
      simp [cyclicSupercharge_star_eq_sq g, pow_two]
    _ = Q := by
      calc
        Q ^ 2 * Q ^ 2 = Q ^ 4 := by
          simp only [pow_two]
          noncomm_ring
        _ = Q := q_pow_four g

theorem cyclicSupercharge_moorePenrose_inverse_eq_square :
    IsMoorePenroseInverse Q (Q ^ 2) := by
  refine IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · calc
      Q * Q ^ 2 * Q = Q ^ 4 := by simp [pow_succ, pow_two, mul_assoc]
      _ = Q := q_pow_four g
  · calc
      Q ^ 2 * Q * Q ^ 2 = Q ^ 5 := by simp [pow_succ, pow_two, mul_assoc]
      _ = Q ^ 2 := q_pow_five g
  · calc
      star (Q * Q ^ 2) = star (Q ^ 2) * star Q := by rw [star_mul]
      _ = Q * Q ^ 2 := by
        rw [star_q_pow_two g, cyclicSupercharge_star_eq_sq g]
        simp only [pow_two]
  · calc
      star (Q ^ 2 * Q) = star Q * star (Q ^ 2) := by rw [star_mul]
      _ = Q ^ 2 * Q := by
        rw [cyclicSupercharge_star_eq_sq g, star_q_pow_two g]
        simp only [pow_two]

theorem cyclicSupercharge_drazin_projector_eq_hamiltonian :
    Drazin_Projector Q (Q ^ 2) 1
        (cyclicSupercharge_drazin_inverse_eq_square g) = H := by
  simp only [Drazin_Projector]
  rw [show Q * Q ^ 2 = Q ^ 3 by simp [pow_succ, pow_two, mul_assoc]]
  exact q_pow_three g

theorem cyclicSupercharge_drazin_residue_projector_eq_defect :
    Drazin_ResidueProjector Q (Q ^ 2) 1
        (cyclicSupercharge_drazin_inverse_eq_square g) = g.P0 := by
  rw [Drazin_ResidueProjector, cyclicSupercharge_drazin_projector_eq_hamiltonian g,
    susyHamiltonian_eq_one_sub_defect g]
  noncomm_ring

theorem cyclicSupercharge_moorePenrose_range_projector_eq_hamiltonian :
    MP_Projector Q (Q ^ 2)
        (cyclicSupercharge_moorePenrose_inverse_eq_square g) = H := by
  simp only [MP_Projector]
  rw [show Q * Q ^ 2 = Q ^ 3 by simp [pow_succ, pow_two, mul_assoc]]
  exact q_pow_three g

end InfoGeometry.Canonical.ToeplitzCuntzThreeGeneralizedInverse
