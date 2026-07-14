import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Clifford.ClNN
import InfoGeometry.Clifford.ConformalLift55
import Mathlib.Tactic.NoncommRing

/-!
# Conformal Generator Lemmas for Cl(5,5)

This file isolates the lowest-level definitions and algebraic proofs of the
conformal generators for the $C\ell(5,5)$ representation.
-/

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ConformalLift55

noncomputable section

namespace InfoGeometry.Clifford.ConformalLieAlgebra55

def u5 : Alg 5 := gammaHeadNullMinus 4
def v5 : Alg 5 := gammaHeadNullPlus 4
def u4 : Alg 5 := gammaTail 4 (headNullMinus 3)
def v4 : Alg 5 := gammaTail 4 (headNullPlus 3)

def D5 : Alg 5 := (1 / 2 : ℝ) • (u5 * v5 - v5 * u5)
def D4 : Alg 5 := (1 / 2 : ℝ) • (u4 * v4 - v4 * u4)
def D : Alg 5 := D5 + D4

def J5 : Alg 5 := u5 - v5
def J4 : Alg 5 := u4 - v4
def J : Alg 5 := J5 * J4

/-! ### Orthogonal Anticommutativity -/

theorem u5_u4_anti : u5 * u4 = - (u4 * u5) := eq_neg_of_add_eq_zero_left (gammaHeadNullMinus_mul_gammaTail_add_swap 4 (headNullMinus 3))
theorem v5_u4_anti : v5 * u4 = - (u4 * v5) := eq_neg_of_add_eq_zero_left (gammaHeadNullPlus_mul_gammaTail_add_swap 4 (headNullMinus 3))
theorem u5_v4_anti : u5 * v4 = - (v4 * u5) := eq_neg_of_add_eq_zero_left (gammaHeadNullMinus_mul_gammaTail_add_swap 4 (headNullPlus 3))
theorem v5_v4_anti : v5 * v4 = - (v4 * v5) := eq_neg_of_add_eq_zero_left (gammaHeadNullPlus_mul_gammaTail_add_swap 4 (headNullPlus 3))

theorem J5_J4_anti : J5 * J4 = - (J4 * J5) := by
  dsimp [J5, J4]
  calc
    (u5 - v5) * (u4 - v4) = u5 * u4 - u5 * v4 - v5 * u4 + v5 * v4 := by noncomm_ring
    _ = - (u4 * u5) - (- (v4 * u5)) - (- (u4 * v5)) + (- (v4 * v5)) := by rw [u5_u4_anti, u5_v4_anti, v5_u4_anti, v5_v4_anti]
    _ = - (u4 * u5 - u4 * v5 - v4 * u5 + v4 * v5) := by noncomm_ring
    _ = - ((u4 - v4) * (u5 - v5)) := by noncomm_ring

/-! ### Square Rules -/

theorem J5_sq : J5 * J5 = -1 := by
  dsimp [J5, u5, v5]
  rw [sub_mul, mul_sub, mul_sub]
  have hu : gammaHeadNullMinus 4 * gammaHeadNullMinus 4 = 0 := gammaHeadNullMinus_sq 4
  have hv : gammaHeadNullPlus 4 * gammaHeadNullPlus 4 = 0 := gammaHeadNullPlus_sq 4
  have huv : gammaHeadNullMinus 4 * gammaHeadNullPlus 4 + gammaHeadNullPlus 4 * gammaHeadNullMinus 4 = 1 := 
    gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap 4
  rw [hu, hv]
  simp only [zero_sub, sub_zero]
  rw [sub_eq_add_neg, ← neg_add]
  rw [huv]

theorem J4_sq : J4 * J4 = -1 := by
  dsimp [J4, u4, v4]
  rw [sub_mul, mul_sub, mul_sub]
  have hu : gammaTail 4 (headNullMinus 3) * gammaTail 4 (headNullMinus 3) = 0 := by
    rw [gammaTail, CliffordAlgebra.ι_sq_scalar, quad_tailLift, headNullMinus_isotropic]
    simp
  have hv : gammaTail 4 (headNullPlus 3) * gammaTail 4 (headNullPlus 3) = 0 := by
    rw [gammaTail, CliffordAlgebra.ι_sq_scalar, quad_tailLift, headNullPlus_isotropic]
    simp
  have huv : gammaTail 4 (headNullMinus 3) * gammaTail 4 (headNullPlus 3) + 
      gammaTail 4 (headNullPlus 3) * gammaTail 4 (headNullMinus 3) = 1 := by
    have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := Quad 5) (tailLift 4 (headNullMinus 3)) (tailLift 4 (headNullPlus 3))
    have h_polar : QuadraticMap.polar (Quad 5) (tailLift 4 (headNullMinus 3)) (tailLift 4 (headNullPlus 3)) = 1 := by
      rw [QuadraticMap.polar, quad_tailLift, quad_tailLift]
      have h_sum : tailLift 4 (headNullMinus 3) + tailLift 4 (headNullPlus 3) = tailLift 4 (headNullMinus 3 + headNullPlus 3) := by
        simp [tailLift, headNullMinus, headNullPlus, headPair]
      rw [h_sum, quad_tailLift]
      exact polar_headNullMinus_headNullPlus 3
    rw [h_polar] at h
    exact h
  rw [hu, hv]
  simp only [zero_sub, sub_zero]
  rw [sub_eq_add_neg, ← neg_add]
  rw [huv]

theorem J_sq : J * J = -1 := by
  dsimp [J]
  have h1 : J5 * J4 * (J5 * J4) = J5 * (J4 * J5) * J4 := by noncomm_ring
  rw [h1]
  have h2 : J4 * J5 = - (J5 * J4) := eq_neg_of_add_eq_zero_left (by rw [J5_J4_anti, add_neg_cancel])
  rw [h2]
  have h3 : J5 * - (J5 * J4) * J4 = - (J5 * J5 * (J4 * J4)) := by noncomm_ring
  rw [h3]
  rw [J5_sq, J4_sq]
  noncomm_ring

/-! ### Dilation Action -/

theorem u5_sq : u5 * u5 = 0 := gammaHeadNullMinus_sq 4
theorem v5_sq : v5 * v5 = 0 := gammaHeadNullPlus_sq 4
theorem u5_v5_add_v5_u5 : u5 * v5 + v5 * u5 = 1 := gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap 4

theorem adD5_u5 : D5 * u5 - u5 * D5 = u5 := by
  dsimp [D5]
  rw [smul_mul_assoc, Algebra.mul_smul_comm, sub_mul, mul_sub]
  have hsub' : v5 * u5 + u5 * v5 = 1 := by
    simpa [add_comm] using u5_v5_add_v5_u5
  have huv5 : u5 * (v5 * u5) = u5 := by
    have hvu5 : v5 * u5 = 1 - u5 * v5 := by
      exact eq_sub_of_add_eq hsub'
    calc
      u5 * (v5 * u5) = u5 * (1 - u5 * v5) := by rw [hvu5]
      _ = u5 - u5 * (u5 * v5) := by rw [mul_sub]; simp
      _ = u5 - (u5 * u5) * v5 := by rw [← mul_assoc]
      _ = u5 - 0 := by rw [u5_sq]; simp
      _ = u5 := by simp
  have hvu5'' : v5 * u5 * u5 = 0 := by
    calc
      v5 * u5 * u5 = v5 * (u5 * u5) := by noncomm_ring
      _ = v5 * 0 := by rw [u5_sq]
      _ = 0 := by simp
  have huv5sq : u5 * (u5 * v5) = 0 := by
    calc
      u5 * (u5 * v5) = (u5 * u5) * v5 := by rw [mul_assoc]
      _ = 0 * v5 := by rw [u5_sq]
      _ = 0 := by simp
  have hmul : u5 * (u5 * v5 - v5 * u5) = -u5 := by
    calc
      u5 * (u5 * v5 - v5 * u5) = u5 * (u5 * v5) - u5 * (v5 * u5) := by rw [mul_sub]
      _ = 0 - u5 := by rw [huv5sq, huv5]
      _ = -u5 := by rw [zero_sub]
  have hinner : (u5 * v5 * u5 - v5 * u5 * u5) - (u5 * (u5 * v5) - u5 * (v5 * u5)) = (2 : ℝ) • u5 := by
    have h1 : u5 * v5 * u5 = u5 := by
      calc
        u5 * v5 * u5 = u5 * (v5 * u5) := by noncomm_ring
        _ = u5 := huv5
    calc
      (u5 * v5 * u5 - v5 * u5 * u5) - (u5 * (u5 * v5) - u5 * (v5 * u5))
          = (u5 - 0) - (0 - u5) := by rw [h1, hvu5'', huv5sq, huv5]
      _ = u5 + u5 := by abel
      _ = (2 : ℝ) • u5 := by rw [two_smul]
  have hsmul :
      (1 / 2 : ℝ) • (u5 * v5 * u5 - v5 * u5 * u5) - (1 / 2 : ℝ) • (u5 * (u5 * v5) - u5 * (v5 * u5)) =
        (1 / 2 : ℝ) • ((u5 * v5 * u5 - v5 * u5 * u5) - (u5 * (u5 * v5) - u5 * (v5 * u5))) := by
    simp [sub_eq_add_neg, smul_add, smul_neg, add_assoc]
  calc
    (1 / 2 : ℝ) • (u5 * v5 * u5 - v5 * u5 * u5) - (1 / 2 : ℝ) • (u5 * (u5 * v5) - u5 * (v5 * u5))
        = (1 / 2 : ℝ) • ((u5 * v5 * u5 - v5 * u5 * u5) - (u5 * (u5 * v5) - u5 * (v5 * u5))) := by
          simpa using hsmul
    _ = (1 / 2 : ℝ) • ((2 : ℝ) • u5) := by rw [hinner]
    _ = u5 := by
      rw [smul_smul]
      norm_num

theorem h_v4_u5_anti : v4 * u5 = - (u5 * v4) := by
  have h : u5 * v4 + v4 * u5 = 0 := by rw [u5_v4_anti]; exact neg_add_cancel (v4 * u5)
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm, h])

theorem h_u4_u5_anti : u4 * u5 = - (u5 * u4) := by
  have h : u5 * u4 + u4 * u5 = 0 := by rw [u5_u4_anti]; exact neg_add_cancel (u4 * u5)
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm, h])

theorem adD4_u5 : D4 * u5 - u5 * D4 = 0 := by
  dsimp [D4]
  rw [smul_mul_assoc, Algebra.mul_smul_comm, sub_mul, mul_sub, ← smul_sub]
  have h1 : u4 * v4 * u5 = u5 * (u4 * v4) := by
    calc
      u4 * v4 * u5 = u4 * (v4 * u5) := by noncomm_ring
      _ = u4 * (- (u5 * v4)) := by rw [h_v4_u5_anti]
      _ = - (u4 * u5 * v4) := by noncomm_ring
      _ = - (- (u5 * u4) * v4) := by rw [h_u4_u5_anti]
      _ = u5 * u4 * v4 := by noncomm_ring
      _ = u5 * (u4 * v4) := by noncomm_ring
  have h2 : v4 * u4 * u5 = u5 * (v4 * u4) := by
    calc
      v4 * u4 * u5 = v4 * (u4 * u5) := by noncomm_ring
      _ = v4 * (- (u5 * u4)) := by rw [h_u4_u5_anti]
      _ = - (v4 * u5 * u4) := by noncomm_ring
      _ = - (- (u5 * v4) * u4) := by rw [h_v4_u5_anti]
      _ = u5 * v4 * u4 := by noncomm_ring
      _ = u5 * (v4 * u4) := by noncomm_ring
  rw [h1, h2]
  have h_sub : u5 * (u4 * v4) - u5 * (v4 * u4) - (u5 * (u4 * v4) - u5 * (v4 * u4)) = 0 := by abel
  rw [h_sub]
  exact smul_zero (1 / 2 : ℝ)
theorem adD_u5 : D * u5 - u5 * D = u5 := by
  dsimp [D]
  have h1 : D5 * u5 - u5 * D5 = u5 := adD5_u5
  have h2 : D4 * u5 - u5 * D4 = 0 := adD4_u5
  calc
    (D5 + D4) * u5 - u5 * (D5 + D4) = D5 * u5 + D4 * u5 - (u5 * D5 + u5 * D4) := by noncomm_ring
    _ = (D5 * u5 - u5 * D5) + (D4 * u5 - u5 * D4) := by abel
    _ = u5 + 0 := by rw [h1, h2]
    _ = u5 := by exact add_zero u5

theorem u4_sq : u4 * u4 = 0 := by
  dsimp [u4]; rw [gammaTail, CliffordAlgebra.ι_sq_scalar, quad_tailLift, headNullMinus_isotropic]; simp
theorem v4_sq : v4 * v4 = 0 := by
  dsimp [v4]; rw [gammaTail, CliffordAlgebra.ι_sq_scalar, quad_tailLift, headNullPlus_isotropic]; simp

theorem u4_v4_add_v4_u4 : u4 * v4 + v4 * u4 = 1 := by
  dsimp [u4, v4]
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := Quad 5) (tailLift 4 (headNullMinus 3)) (tailLift 4 (headNullPlus 3))
  have h_polar : QuadraticMap.polar (Quad 5) (tailLift 4 (headNullMinus 3)) (tailLift 4 (headNullPlus 3)) = 1 := by
    rw [QuadraticMap.polar, quad_tailLift, quad_tailLift]
    have h_sum : tailLift 4 (headNullMinus 3) + tailLift 4 (headNullPlus 3) = tailLift 4 (headNullMinus 3 + headNullPlus 3) := by
      simp [tailLift, headNullMinus, headNullPlus, headPair]
    rw [h_sum, quad_tailLift]
    exact polar_headNullMinus_headNullPlus 3
  rw [h_polar] at h
  exact h

theorem h_u5_u4_anti_2 : u5 * u4 = - (u4 * u5) := u5_u4_anti
theorem h_v5_u4_anti_2 : v5 * u4 = - (u4 * v5) := v5_u4_anti

theorem adD4_u4 : D4 * u4 - u4 * D4 = u4 := by
  dsimp [D4]
  rw [smul_mul_assoc, Algebra.mul_smul_comm, sub_mul, mul_sub, ← smul_sub]
  have huv : u4 * v4 * u4 = u4 := by
    have hsub : u4 * v4 = 1 - v4 * u4 := by
      exact eq_sub_of_add_eq u4_v4_add_v4_u4
    calc
      u4 * v4 * u4 = (1 - v4 * u4) * u4 := by rw [hsub]
      _ = u4 - v4 * u4 * u4 := by rw [sub_mul, one_mul]
      _ = u4 - v4 * (u4 * u4) := by rw [mul_assoc]
      _ = u4 := by rw [u4_sq, mul_zero, sub_zero]
  have hvuu : v4 * u4 * u4 = 0 := by
    calc
      v4 * u4 * u4 = v4 * (u4 * u4) := by noncomm_ring
      _ = 0 := by rw [u4_sq, mul_zero]
  have huuv4 : u4 * (u4 * v4) = 0 := by
    calc
      u4 * (u4 * v4) = (u4 * u4) * v4 := by noncomm_ring
      _ = 0 := by rw [u4_sq, zero_mul]
  have huv0 : u4 * (v4 * u4) = u4 := by
    have hsub : v4 * u4 = 1 - u4 * v4 := by
      have h_add : v4 * u4 + u4 * v4 = 1 := by
        have h_comm := u4_v4_add_v4_u4
        rw [add_comm] at h_comm
        exact h_comm
      exact eq_sub_of_add_eq h_add
    calc
      u4 * (v4 * u4) = u4 * (1 - u4 * v4) := by rw [hsub]
      _ = u4 - u4 * (u4 * v4) := by rw [mul_sub, mul_one]
      _ = u4 - 0 := by rw [huuv4]
      _ = u4 := by exact sub_zero u4
  have h_calc : u4 * v4 * u4 - v4 * u4 * u4 - (u4 * (u4 * v4) - u4 * (v4 * u4)) = u4 + u4 := by
    rw [huv, hvuu, huuv4, huv0]
    abel
  rw [h_calc]
  have h_two : u4 + u4 = (2 : ℝ) • u4 := by
    have h_one : u4 = (1 : ℝ) • u4 := by exact Eq.symm (one_smul ℝ u4)
    nth_rw 1 [h_one]
    nth_rw 2 [h_one]
    rw [← add_smul]
    norm_num
  rw [h_two, smul_smul]
  norm_num
theorem adD5_u4 : D5 * u4 - u4 * D5 = 0 := by
  dsimp [D5]
  rw [smul_mul_assoc, Algebra.mul_smul_comm, sub_mul, mul_sub, ← smul_sub]
  have h1 : u5 * v5 * u4 = u4 * (u5 * v5) := by
    calc
      u5 * v5 * u4 = u5 * (v5 * u4) := by noncomm_ring
      _ = u5 * (- (u4 * v5)) := by rw [h_v5_u4_anti_2]
      _ = - (u5 * u4 * v5) := by noncomm_ring
      _ = - (- (u4 * u5) * v5) := by rw [h_u5_u4_anti_2]
      _ = u4 * u5 * v5 := by noncomm_ring
      _ = u4 * (u5 * v5) := by noncomm_ring
  have h2 : v5 * u5 * u4 = u4 * (v5 * u5) := by
    calc
      v5 * u5 * u4 = v5 * (u5 * u4) := by noncomm_ring
      _ = v5 * (- (u4 * u5)) := by rw [h_u5_u4_anti_2]
      _ = - (v5 * u4 * u5) := by noncomm_ring
      _ = - (- (u4 * v5) * u5) := by rw [h_v5_u4_anti_2]
      _ = u4 * v5 * u5 := by noncomm_ring
      _ = u4 * (v5 * u5) := by noncomm_ring
  rw [h1, h2]
  have h_sub : u4 * (u5 * v5) - u4 * (v5 * u5) - (u4 * (u5 * v5) - u4 * (v5 * u5)) = 0 := by abel
  rw [h_sub]
  exact smul_zero (1 / 2 : ℝ)
theorem adD_u4 : D * u4 - u4 * D = u4 := by
  dsimp [D]
  have h1 : D5 * u4 - u4 * D5 = 0 := adD5_u4
  have h2 : D4 * u4 - u4 * D4 = u4 := adD4_u4
  calc
    (D5 + D4) * u4 - u4 * (D5 + D4) = D5 * u4 + D4 * u4 - (u4 * D5 + u4 * D4) := by noncomm_ring
    _ = (D5 * u4 - u4 * D5) + (D4 * u4 - u4 * D4) := by abel
    _ = 0 + u4 := by rw [h1, h2]
    _ = u4 := by exact zero_add u4

/-! ### Theta Rules -/

def thetaOp (x : Alg 5) : Alg 5 := - J * x * J

theorem theta_inv (x : Alg 5) : thetaOp (thetaOp x) = x := by
  dsimp [thetaOp]
  calc
    - J * (- J * x * J) * J = (- J * - J) * x * (J * J) := by noncomm_ring
    _ = (J * J) * x * (J * J) := by noncomm_ring
    _ = (-1 : Alg 5) * x * (-1 : Alg 5) := by rw [J_sq]
    _ = x := by noncomm_ring

/-! ### Cross-Sector Anticommutation -/

theorem J4_u5_anti : J4 * u5 = - (u5 * J4) := by
  dsimp [J4]
  have h1 : u4 * u5 = - (u5 * u4) := by
    have h_add : u4 * u5 + u5 * u4 = 0 := by rw [u5_u4_anti]; exact add_neg_cancel (u4 * u5)
    exact eq_neg_of_add_eq_zero_left h_add
  have h2 : v4 * u5 = - (u5 * v4) := by
    have h_add : v4 * u5 + u5 * v4 = 0 := by rw [u5_v4_anti]; exact add_neg_cancel (v4 * u5)
    exact eq_neg_of_add_eq_zero_left h_add
  calc
    (u4 - v4) * u5 = u4 * u5 - v4 * u5 := by noncomm_ring
    _ = - (u5 * u4) - (- (u5 * v4)) := by rw [h1, h2]
    _ = - (u5 * (u4 - v4)) := by noncomm_ring

theorem J4_v5_anti : J4 * v5 = - (v5 * J4) := by
  dsimp [J4]
  have h1 : u4 * v5 = - (v5 * u4) := by
    have h_add : u4 * v5 + v5 * u4 = 0 := by rw [v5_u4_anti]; exact add_neg_cancel (u4 * v5)
    exact eq_neg_of_add_eq_zero_left h_add
  have h2 : v4 * v5 = - (v5 * v4) := by
    have h_add : v4 * v5 + v5 * v4 = 0 := by rw [v5_v4_anti]; exact add_neg_cancel (v4 * v5)
    exact eq_neg_of_add_eq_zero_left h_add
  calc
    (u4 - v4) * v5 = u4 * v5 - v4 * v5 := by noncomm_ring
    _ = - (v5 * u4) - (- (v5 * v4)) := by rw [h1, h2]
    _ = - (v5 * (u4 - v4)) := by noncomm_ring

theorem J5_u4_anti : J5 * u4 = - (u4 * J5) := by
  dsimp [J5]
  calc
    (u5 - v5) * u4 = u5 * u4 - v5 * u4 := by noncomm_ring
    _ = - (u4 * u5) - (- (u4 * v5)) := by rw [u5_u4_anti, v5_u4_anti]
    _ = - (u4 * (u5 - v5)) := by noncomm_ring

theorem J5_v4_anti : J5 * v4 = - (v4 * J5) := by
  dsimp [J5]
  calc
    (u5 - v5) * v4 = u5 * v4 - v5 * v4 := by noncomm_ring
    _ = - (v4 * u5) - (- (v4 * v5)) := by rw [u5_v4_anti, v5_v4_anti]
    _ = - (v4 * (u5 - v5)) := by noncomm_ring

/-! ### Theta Generator Reflection Laws -/

theorem theta_u5 : thetaOp u5 = v5 := by
  dsimp [thetaOp, J]
  have hj: J4 * J5 = - (J5 * J4) := by
    have h_add : J4 * J5 + J5 * J4 = 0 := by rw [J5_J4_anti]; exact add_neg_cancel (J4 * J5)
    exact eq_neg_of_add_eq_zero_left h_add
  have step1 : - (J5 * J4) * u5 * (J5 * J4) = - J5 * (J4 * u5) * J5 * J4 := by noncomm_ring
  have step2 : - J5 * (J4 * u5) * J5 * J4 = - J5 * (- (u5 * J4)) * J5 * J4 := by rw [J4_u5_anti]
  have step3 : - J5 * (- (u5 * J4)) * J5 * J4 = J5 * u5 * (J4 * J5) * J4 := by noncomm_ring
  have step4 : J5 * u5 * (J4 * J5) * J4 = J5 * u5 * (- (J5 * J4)) * J4 := by rw [hj]
  have step5 : J5 * u5 * (- (J5 * J4)) * J4 = - (J5 * u5 * J5) * (J4 * J4) := by noncomm_ring
  have step6 : - (J5 * u5 * J5) * (J4 * J4) = - (J5 * u5 * J5) * (-1 : Alg 5) := by rw [J4_sq]
  have step7 : - (J5 * u5 * J5) * (-1 : Alg 5) = J5 * u5 * J5 := by noncomm_ring
  have step8 : J5 * u5 * J5 = (u5 - v5) * u5 * (u5 - v5) := by rfl
  have step9 : (u5 - v5) * u5 * (u5 - v5) = u5 * u5 * u5 - u5 * u5 * v5 - v5 * u5 * u5 + v5 * u5 * v5 := by noncomm_ring
  have step10 : u5 * u5 * u5 - u5 * u5 * v5 - v5 * u5 * u5 + v5 * u5 * v5 = v5 * u5 * v5 := by
    have h1 : v5 * u5 * u5 = v5 * (u5 * u5) := by noncomm_ring
    have h2 : u5 * u5 * u5 = (u5 * u5) * u5 := by noncomm_ring
    have h3 : u5 * u5 * v5 = (u5 * u5) * v5 := by noncomm_ring
    rw [h1, h2, h3, u5_sq]
    noncomm_ring
  have step11 : v5 * u5 * v5 = v5 * (u5 * v5) := by noncomm_ring
  have step12 : v5 * (u5 * v5) = v5 * (1 - v5 * u5) := by
    have h_sub : u5 * v5 = 1 - v5 * u5 := by
      have h_add := u5_v5_add_v5_u5
      exact eq_sub_of_add_eq h_add
    rw [h_sub]
  have step13 : v5 * (1 - v5 * u5) = v5 - v5 * v5 * u5 := by noncomm_ring
  have step14 : v5 - v5 * v5 * u5 = v5 := by
    have h1 : v5 * v5 * u5 = (v5 * v5) * u5 := by noncomm_ring
    rw [h1, v5_sq]
    noncomm_ring
  rw [step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11, step12, step13, step14]

theorem theta_v5 : thetaOp v5 = u5 := by
  dsimp [thetaOp, J]
  have hj: J4 * J5 = - (J5 * J4) := by
    have h_add : J4 * J5 + J5 * J4 = 0 := by rw [J5_J4_anti]; exact add_neg_cancel (J4 * J5)
    exact eq_neg_of_add_eq_zero_left h_add
  have step1 : - (J5 * J4) * v5 * (J5 * J4) = - J5 * (J4 * v5) * J5 * J4 := by noncomm_ring
  have step2 : - J5 * (J4 * v5) * J5 * J4 = - J5 * (- (v5 * J4)) * J5 * J4 := by rw [J4_v5_anti]
  have step3 : - J5 * (- (v5 * J4)) * J5 * J4 = J5 * v5 * (J4 * J5) * J4 := by noncomm_ring
  have step4 : J5 * v5 * (J4 * J5) * J4 = J5 * v5 * (- (J5 * J4)) * J4 := by rw [hj]
  have step5 : J5 * v5 * (- (J5 * J4)) * J4 = - (J5 * v5 * J5) * (J4 * J4) := by noncomm_ring
  have step6 : - (J5 * v5 * J5) * (J4 * J4) = - (J5 * v5 * J5) * (-1 : Alg 5) := by rw [J4_sq]
  have step7 : - (J5 * v5 * J5) * (-1 : Alg 5) = J5 * v5 * J5 := by noncomm_ring
  have step8 : J5 * v5 * J5 = (u5 - v5) * v5 * (u5 - v5) := by rfl
  have step9 : (u5 - v5) * v5 * (u5 - v5) = u5 * v5 * u5 - u5 * v5 * v5 - v5 * v5 * u5 + v5 * v5 * v5 := by noncomm_ring
  have step10 : u5 * v5 * u5 - u5 * v5 * v5 - v5 * v5 * u5 + v5 * v5 * v5 = u5 * v5 * u5 := by
    have h1 : u5 * v5 * v5 = u5 * (v5 * v5) := by noncomm_ring
    have h2 : v5 * v5 * u5 = (v5 * v5) * u5 := by noncomm_ring
    have h3 : v5 * v5 * v5 = (v5 * v5) * v5 := by noncomm_ring
    rw [h1, h2, h3, v5_sq]
    noncomm_ring
  have step11 : u5 * v5 * u5 = u5 * (v5 * u5) := by noncomm_ring
  have step12 : u5 * (v5 * u5) = u5 * (1 - u5 * v5) := by
    have h_sub : v5 * u5 = 1 - u5 * v5 := by
      have h_add : v5 * u5 + u5 * v5 = 1 := by rw [add_comm]; exact u5_v5_add_v5_u5
      exact eq_sub_of_add_eq h_add
    rw [h_sub]
  have step13 : u5 * (1 - u5 * v5) = u5 - u5 * u5 * v5 := by noncomm_ring
  have step14 : u5 - u5 * u5 * v5 = u5 := by
    have h1 : u5 * u5 * v5 = (u5 * u5) * v5 := by noncomm_ring
    rw [h1, u5_sq]
    noncomm_ring
  rw [step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11, step12, step13, step14]

theorem theta_u4 : thetaOp u4 = v4 := by
  dsimp [thetaOp, J]
  have hj: J4 * J5 = - (J5 * J4) := by
    have h_add : J4 * J5 + J5 * J4 = 0 := by rw [J5_J4_anti]; exact add_neg_cancel (J4 * J5)
    exact eq_neg_of_add_eq_zero_left h_add
  have step1 : - (J5 * J4) * u4 * (J5 * J4) = - J5 * (J4 * u4) * J5 * J4 := by noncomm_ring
  have step2 : - J5 * (J4 * u4) * J5 * J4 = - J5 * ((u4 - v4) * u4) * J5 * J4 := by rfl
  have step3 : - J5 * ((u4 - v4) * u4) * J5 * J4 = - J5 * (u4 * u4 - v4 * u4) * J5 * J4 := by noncomm_ring
  have step4 : - J5 * (u4 * u4 - v4 * u4) * J5 * J4 = - J5 * (0 - v4 * u4) * J5 * J4 := by rw [u4_sq]
  have step5 : - J5 * (0 - v4 * u4) * J5 * J4 = J5 * (v4 * u4) * J5 * J4 := by noncomm_ring
  have step6 : J5 * (v4 * u4) * J5 * J4 = J5 * (1 - u4 * v4) * J5 * J4 := by
    have h_sub : v4 * u4 = 1 - u4 * v4 := by
      have h_add : v4 * u4 + u4 * v4 = 1 := by rw [add_comm]; exact u4_v4_add_v4_u4
      exact eq_sub_of_add_eq h_add
    rw [h_sub]
  have step7 : J5 * (1 - u4 * v4) * J5 * J4 = J5 * J5 * J4 - J5 * u4 * v4 * J5 * J4 := by noncomm_ring
  have step8 : J5 * J5 * J4 - J5 * u4 * v4 * J5 * J4 = -1 * J4 - J5 * u4 * v4 * J5 * J4 := by
    have h1 : J5 * J5 * J4 = (J5 * J5) * J4 := by noncomm_ring
    rw [h1, J5_sq]
  have step9 : -1 * J4 - J5 * u4 * v4 * J5 * J4 = - J4 - J5 * u4 * v4 * J5 * J4 := by noncomm_ring
  have step10 : - J4 - J5 * u4 * v4 * J5 * J4 = - J4 - (J5 * u4) * v4 * J5 * J4 := by noncomm_ring
  have step11 : - J4 - (J5 * u4) * v4 * J5 * J4 = - J4 - (- (u4 * J5)) * v4 * J5 * J4 := by rw [J5_u4_anti]
  have step12 : - J4 - (- (u4 * J5)) * v4 * J5 * J4 = - J4 + u4 * (J5 * v4) * J5 * J4 := by noncomm_ring
  have step13 : - J4 + u4 * (J5 * v4) * J5 * J4 = - J4 + u4 * (- (v4 * J5)) * J5 * J4 := by rw [J5_v4_anti]
  have step14 : - J4 + u4 * (- (v4 * J5)) * J5 * J4 = - J4 - u4 * v4 * (J5 * J5) * J4 := by noncomm_ring
  have step15 : - J4 - u4 * v4 * (J5 * J5) * J4 = - J4 - u4 * v4 * (-1 : Alg 5) * J4 := by
    have h1 : u4 * v4 * (J5 * J5) * J4 = u4 * v4 * (J5 * J5) * J4 := by noncomm_ring
    rw [h1, J5_sq]
  have step16 : - J4 - u4 * v4 * (-1 : Alg 5) * J4 = - J4 + u4 * v4 * J4 := by noncomm_ring
  have step17 : - J4 + u4 * v4 * J4 = - (u4 - v4) + u4 * v4 * (u4 - v4) := by rfl
  have step18 : - (u4 - v4) + u4 * v4 * (u4 - v4) = - u4 + v4 + u4 * v4 * u4 - u4 * v4 * v4 := by noncomm_ring
  have step19 : - u4 + v4 + u4 * v4 * u4 - u4 * v4 * v4 = - u4 + v4 + u4 * (v4 * u4) - u4 * (v4 * v4) := by noncomm_ring
  have step20 : - u4 + v4 + u4 * (v4 * u4) - u4 * (v4 * v4) = - u4 + v4 + u4 * (v4 * u4) - u4 * 0 := by rw [v4_sq]
  have step21 : - u4 + v4 + u4 * (v4 * u4) - u4 * 0 = - u4 + v4 + u4 * (v4 * u4) := by noncomm_ring
  have step22 : - u4 + v4 + u4 * (v4 * u4) = - u4 + v4 + u4 * (1 - u4 * v4) := by
    have h_sub : v4 * u4 = 1 - u4 * v4 := by
      have h_add : v4 * u4 + u4 * v4 = 1 := by rw [add_comm]; exact u4_v4_add_v4_u4
      exact eq_sub_of_add_eq h_add
    rw [h_sub]
  have step23 : - u4 + v4 + u4 * (1 - u4 * v4) = - u4 + v4 + u4 - u4 * u4 * v4 := by noncomm_ring
  have step24 : - u4 + v4 + u4 - u4 * u4 * v4 = - u4 + v4 + u4 - (u4 * u4) * v4 := by noncomm_ring
  have step25 : - u4 + v4 + u4 - (u4 * u4) * v4 = - u4 + v4 + u4 - 0 * v4 := by rw [u4_sq]
  have step26 : - u4 + v4 + u4 - 0 * v4 = v4 := by noncomm_ring
  rw [step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22, step23, step24, step25, step26]

theorem theta_v4 : thetaOp v4 = u4 := by
  dsimp [thetaOp, J]
  have hj: J4 * J5 = - (J5 * J4) := by
    have h_add : J4 * J5 + J5 * J4 = 0 := by rw [J5_J4_anti]; exact add_neg_cancel (J4 * J5)
    exact eq_neg_of_add_eq_zero_left h_add
  have step1 : - (J5 * J4) * v4 * (J5 * J4) = - J5 * (J4 * v4) * J5 * J4 := by noncomm_ring
  have step2 : - J5 * (J4 * v4) * J5 * J4 = - J5 * ((u4 - v4) * v4) * J5 * J4 := by rfl
  have step3 : - J5 * ((u4 - v4) * v4) * J5 * J4 = - J5 * (u4 * v4 - v4 * v4) * J5 * J4 := by noncomm_ring
  have step4 : - J5 * (u4 * v4 - v4 * v4) * J5 * J4 = - J5 * (u4 * v4 - 0) * J5 * J4 := by rw [v4_sq]
  have step5 : - J5 * (u4 * v4 - 0) * J5 * J4 = - J5 * (u4 * v4) * J5 * J4 := by noncomm_ring
  have step6 : - J5 * (u4 * v4) * J5 * J4 = - J5 * (1 - v4 * u4) * J5 * J4 := by
    have h_sub : u4 * v4 = 1 - v4 * u4 := by
      have h_add := u4_v4_add_v4_u4
      exact eq_sub_of_add_eq h_add
    rw [h_sub]
  have step7 : - J5 * (1 - v4 * u4) * J5 * J4 = - J5 * J5 * J4 + J5 * v4 * u4 * J5 * J4 := by noncomm_ring
  have step8 : - J5 * J5 * J4 + J5 * v4 * u4 * J5 * J4 = - (-1 : Alg 5) * J4 + J5 * v4 * u4 * J5 * J4 := by
    have h1 : - J5 * J5 * J4 = - (J5 * J5) * J4 := by noncomm_ring
    rw [h1, J5_sq]
  have step9 : - (-1 : Alg 5) * J4 + J5 * v4 * u4 * J5 * J4 = J4 + J5 * v4 * u4 * J5 * J4 := by noncomm_ring
  have step10 : J4 + J5 * v4 * u4 * J5 * J4 = J4 + (J5 * v4) * u4 * J5 * J4 := by noncomm_ring
  have step11 : J4 + (J5 * v4) * u4 * J5 * J4 = J4 + (- (v4 * J5)) * u4 * J5 * J4 := by rw [J5_v4_anti]
  have step12 : J4 + (- (v4 * J5)) * u4 * J5 * J4 = J4 - v4 * (J5 * u4) * J5 * J4 := by noncomm_ring
  have step13 : J4 - v4 * (J5 * u4) * J5 * J4 = J4 - v4 * (- (u4 * J5)) * J5 * J4 := by rw [J5_u4_anti]
  have step14 : J4 - v4 * (- (u4 * J5)) * J5 * J4 = J4 + v4 * u4 * (J5 * J5) * J4 := by noncomm_ring
  have step15 : J4 + v4 * u4 * (J5 * J5) * J4 = J4 + v4 * u4 * (-1 : Alg 5) * J4 := by
    have h1 : v4 * u4 * (J5 * J5) * J4 = v4 * u4 * (J5 * J5) * J4 := by noncomm_ring
    rw [h1, J5_sq]
  have step16 : J4 + v4 * u4 * (-1 : Alg 5) * J4 = J4 - v4 * u4 * J4 := by noncomm_ring
  have step17 : J4 - v4 * u4 * J4 = (u4 - v4) - v4 * u4 * (u4 - v4) := by rfl
  have step18 : (u4 - v4) - v4 * u4 * (u4 - v4) = u4 - v4 - v4 * u4 * u4 + v4 * u4 * v4 := by noncomm_ring
  have step19 : u4 - v4 - v4 * u4 * u4 + v4 * u4 * v4 = u4 - v4 - v4 * (u4 * u4) + v4 * (u4 * v4) := by noncomm_ring
  have step20 : u4 - v4 - v4 * (u4 * u4) + v4 * (u4 * v4) = u4 - v4 - v4 * 0 + v4 * (u4 * v4) := by rw [u4_sq]
  have step21 : u4 - v4 - v4 * 0 + v4 * (u4 * v4) = u4 - v4 + v4 * (u4 * v4) := by noncomm_ring
  have step22 : u4 - v4 + v4 * (u4 * v4) = u4 - v4 + v4 * (1 - v4 * u4) := by
    have h_sub : u4 * v4 = 1 - v4 * u4 := by
      have h_add := u4_v4_add_v4_u4
      exact eq_sub_of_add_eq h_add
    rw [h_sub]
  have step23 : u4 - v4 + v4 * (1 - v4 * u4) = u4 - v4 + v4 - v4 * v4 * u4 := by noncomm_ring
  have step24 : u4 - v4 + v4 - v4 * v4 * u4 = u4 - v4 + v4 - (v4 * v4) * u4 := by noncomm_ring
  have step25 : u4 - v4 + v4 - (v4 * v4) * u4 = u4 - v4 + v4 - 0 * u4 := by rw [v4_sq]
  have step26 : u4 - v4 + v4 - 0 * u4 = u4 := by noncomm_ring
  rw [step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22, step23, step24, step25, step26]


theorem theta_J : thetaOp J = J := by
  dsimp [thetaOp]
  calc
    - J * J * J = - (J * J) * J := by noncomm_ring
    _ = - (-1 : Alg 5) * J := by rw [J_sq]
    _ = J := by noncomm_ring
theorem theta_mul (a b : Alg 5) : thetaOp (a * b) = thetaOp a * thetaOp b := by
  dsimp [thetaOp]
  calc
    - J * (a * b) * J = - (J * a * b * J) := by noncomm_ring
    _ = - (J * a * 1 * b * J) := by rw [mul_one]
    _ = - (J * a * (- (-1 : Alg 5)) * b * J) := by rw [neg_neg]
    _ = - (J * a * (- (J * J)) * b * J) := by rw [J_sq]
    _ = - J * a * J * (- J * b * J) := by noncomm_ring

theorem theta_D5 : thetaOp D5 = -D5 := by
  dsimp [D5]
  have h_linear : thetaOp ((1 / 2 : ℝ) • (u5 * v5 - v5 * u5)) 
                = (1 / 2 : ℝ) • thetaOp (u5 * v5 - v5 * u5) := by
    dsimp [thetaOp]; noncomm_ring
  rw [h_linear]
  have h_sub : thetaOp (u5 * v5 - v5 * u5) = thetaOp (u5 * v5) - thetaOp (v5 * u5) := by
    dsimp [thetaOp]; noncomm_ring
  rw [h_sub]
  rw [theta_mul, theta_mul]
  rw [theta_u5, theta_v5]
  have h_neg : v5 * u5 - u5 * v5 = - (u5 * v5 - v5 * u5) := by noncomm_ring
  rw [h_neg]
  rw [smul_neg]

theorem theta_D4 : thetaOp D4 = -D4 := by
  dsimp [D4]
  have h_linear : thetaOp ((1 / 2 : ℝ) • (u4 * v4 - v4 * u4)) 
                = (1 / 2 : ℝ) • thetaOp (u4 * v4 - v4 * u4) := by
    dsimp [thetaOp]; noncomm_ring
  rw [h_linear]
  have h_sub : thetaOp (u4 * v4 - v4 * u4) = thetaOp (u4 * v4) - thetaOp (v4 * u4) := by
    dsimp [thetaOp]; noncomm_ring
  rw [h_sub]
  rw [theta_mul, theta_mul]
  rw [theta_u4, theta_v4]
  have h_neg : v4 * u4 - u4 * v4 = - (u4 * v4 - v4 * u4) := by noncomm_ring
  rw [h_neg]
  rw [smul_neg]

theorem theta_D : thetaOp D = -D := by
  dsimp [D]
  have h_add : thetaOp (D5 + D4) = thetaOp D5 + thetaOp D4 := by
    dsimp [thetaOp]; noncomm_ring
  have h1 : thetaOp D5 + thetaOp D4 = -D5 + -D4 := by rw [theta_D5, theta_D4]
  rw [h_add, h1]
  have h2 : -D5 + -D4 = -(D5 + D4) := by abel
  rw [h2]


