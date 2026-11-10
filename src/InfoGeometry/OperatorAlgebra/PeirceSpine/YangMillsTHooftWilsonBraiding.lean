/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.NoncommRing

namespace OperatorAlgebra.PeirceSpine.YangMillsTHooftWilsonBraiding

variable {B : Type*} [Ring B] [StarRing B]

/-!
### 0. Universal Additive & Ring Cancellation Helpers
-/

omit [StarRing B] in
private theorem sub_add_self (x y : B) : (x - y) + y = x := by
  calc (x - y) + y
    _ = (x + -y) + y := by rw [sub_eq_add_neg]
    _ = x + (-y + y) := by rw [add_assoc]
    _ = x + (y + -y) := by rw [add_comm (-y) y]
    _ = x + (y - y) := by rw [← sub_eq_add_neg]
    _ = x + 0 := by rw [sub_self]
    _ = x := by rw [add_zero]

omit [StarRing B] in
private theorem add_sub_self_right (x y : B) : (x + y) - y = x := by
  calc (x + y) - y
    _ = (x + y) + -y := by rw [sub_eq_add_neg]
    _ = x + (y + -y) := by rw [add_assoc]
    _ = x + (y - y) := by rw [← sub_eq_add_neg]
    _ = x + 0 := by rw [sub_self]
    _ = x := by rw [add_zero]

omit [StarRing B] in
private theorem add_sub_self_left (x y : B) : (x + y) - x = y := by
  rw [add_comm x y, add_sub_self_right]

omit [StarRing B] in
private theorem sub_add_eq_sub_sub (a b c : B) : a - (b + c) = (a - b) - c := by
  calc a - (b + c)
    _ = a + -(b + c) := by rw [sub_eq_add_neg]
    _ = a + (-c + -b) := by rw [neg_add_rev]
    _ = a + (-b + -c) := by rw [add_comm (-c) (-b)]
    _ = (a + -b) + -c := by rw [← add_assoc]
    _ = (a - b) - c := by rw [← sub_eq_add_neg, ← sub_eq_add_neg]

omit [StarRing B] in
private theorem add_add_sub_cancel (a b : B) : (a + b) + (a - b) = a + a := by
  calc (a + b) + (a - b)
    _ = (a - b) + (a + b) := by rw [add_comm (a + b) (a - b)]
    _ = (a - b) + (b + a) := by rw [add_comm a b]
    _ = ((a - b) + b) + a := by rw [← add_assoc (a - b) b a]
    _ = a + a := by rw [sub_add_self]

omit [StarRing B] in
private theorem sub_add_sub_cancel_two (a b : B) : (a + b) - (a - b) = b + b := by
  have h : a + b = (b + b) + (a - b) := by
    calc a + b
      _ = b + a := by rw [add_comm]
      _ = b + ((a - b) + b) := by rw [sub_add_self a b]
      _ = b + (b + (a - b)) := by rw [add_comm (a - b) b]
      _ = (b + b) + (a - b) := by rw [← add_assoc b b (a - b)]
  calc (a + b) - (a - b)
    _ = ((b + b) + (a - b)) - (a - b) := by rw [h]
    _ = b + b := by rw [add_sub_self_right]

/-!
### 1. Definitions of the Two-Sheeted Projectors, Wilson Loops, and ’t Hooft Operators
-/

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Sheet `+` projector `P = N_+ N_-`. -/
def P (N_plus : B) : B := N_plus * star N_plus

/-- Sheet `-` projector `Q = N_- N_+`. -/
def Q (N_plus : B) : B := star N_plus * N_plus

/-- Total two-sheeted condensate support `V = P + Q`. -/
def V (N_plus : B) : B := N_plus * star N_plus + star N_plus * N_plus

/-- Intrinsic inter-sheet magnetic flux / grading `Σ = P - Q`. -/
def Sigma (N_plus : B) : B := N_plus * star N_plus - star N_plus * N_plus

/-- Self-adjoint gauge vector mode `Φ = N_+ + N_-`. -/
def Phi (N_plus : B) : B := N_plus + star N_plus

/-- Positive-chiral unipotent Wilson holonomy `U_+ = 1 + N_+`. -/
def U_plus (N_plus : B) : B := 1 + N_plus

/-- Inverse positive-chiral unipotent Wilson holonomy `U_+⁻¹ = 1 - N_+`. -/
def U_plus_inv (N_plus : B) : B := 1 - N_plus

/-- Negative-chiral unipotent Wilson holonomy `U_- = 1 + N_-`. -/
def U_minus (N_plus : B) : B := 1 + star N_plus

/-- Inverse negative-chiral unipotent Wilson holonomy `U_-⁻¹ = 1 - N_-`. -/
def U_minus_inv (N_plus : B) : B := 1 - star N_plus

/-- The off-diagonal Peirce-projected Wilson link `U_plus_off = P U_+ Q`
    tunneling from Sheet `-` (`Q`) to Sheet `+` (`P`). -/
def U_plus_off (N_plus : B) : B := P N_plus * U_plus N_plus * Q N_plus

/-- The dual off-diagonal Peirce-projected Wilson link `U_minus_off = Q U_- P`
    tunneling from Sheet `+` (`P`) to Sheet `-` (`Q`). -/
def U_minus_off (N_plus : B) : B := Q N_plus * U_minus N_plus * P N_plus

/-- The inter-sheet `ℤ₂` ’t Hooft disorder loop operator `Z_center = 2P - 1`,
    assigning center phase `+1` to Sheet `+` (`P`) and `-1` to Sheet `-` (`Q`). -/
def Z_center (N_plus : B) : B := P N_plus + P N_plus - 1

/-- The core-vs-vacuum `ℤ₂` vortex monodromy `Z_vortex = 1 - 2V`. -/
def Z_vortex (N_plus : B) : B := 1 - (V N_plus + V N_plus)

/-- The center disorder operator is self-adjoint. -/
theorem Z_center_star (N_plus : B) : star (Z_center N_plus) = Z_center N_plus := by
  dsimp [Z_center, P]
  rw [star_sub, star_add, star_one]
  congr 1
  all_goals rw [star_mul, star_star]

/-!
### 2. Foundational Sheet & Off-Diagonal Wilson Link Identities
-/

theorem star_N_plus_sq (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    star N_plus * star N_plus = 0 := by
  rw [← star_mul, h_nil, star_zero]

theorem star_N_plus_reg (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * N_plus * star N_plus = star N_plus := by
  have h := congrArg star h_reg
  rw [star_mul, star_mul, star_star, ← mul_assoc] at h
  exact h

theorem P_idem (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * P N_plus = P N_plus := by
  dsimp [P]
  rw [← mul_assoc (N_plus * star N_plus) N_plus (star N_plus), h_reg]

theorem Q_idem (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Q N_plus * Q N_plus = Q N_plus := by
  dsimp [Q]
  rw [← mul_assoc (star N_plus * N_plus) (star N_plus) N_plus, star_N_plus_reg N_plus h_reg]

theorem P_mul_Q (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    P N_plus * Q N_plus = 0 := by
  dsimp [P, Q]
  calc (N_plus * star N_plus) * (star N_plus * N_plus)
    _ = N_plus * (star N_plus * (star N_plus * N_plus)) := by
        rw [mul_assoc N_plus (star N_plus) (star N_plus * N_plus)]
    _ = N_plus * ((star N_plus * star N_plus) * N_plus) := by
        rw [← mul_assoc (star N_plus) (star N_plus) N_plus]
    _ = N_plus * (0 * N_plus) := by rw [star_N_plus_sq N_plus h_nil]
    _ = 0 := by rw [zero_mul, mul_zero]

theorem Q_mul_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Q N_plus * P N_plus = 0 := by
  dsimp [P, Q]
  calc (star N_plus * N_plus) * (N_plus * star N_plus)
    _ = star N_plus * (N_plus * (N_plus * star N_plus)) := by
        rw [mul_assoc (star N_plus) N_plus (N_plus * star N_plus)]
    _ = star N_plus * ((N_plus * N_plus) * star N_plus) := by
        rw [← mul_assoc N_plus N_plus (star N_plus)]
    _ = star N_plus * (0 * star N_plus) := by rw [h_nil]
    _ = 0 := by rw [zero_mul, mul_zero]

theorem N_plus_mul_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    N_plus * P N_plus = 0 := by
  dsimp [P]
  rw [← mul_assoc, h_nil, zero_mul]

theorem N_plus_mul_Q (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    N_plus * Q N_plus = N_plus := by
  dsimp [Q]
  rw [← mul_assoc, h_reg]

theorem Q_mul_N_plus (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Q N_plus * N_plus = 0 := by
  dsimp [Q]
  rw [mul_assoc, h_nil, mul_zero]

theorem P_mul_star_N_plus (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    P N_plus * star N_plus = 0 := by
  dsimp [P]
  rw [mul_assoc, star_N_plus_sq N_plus h_nil, mul_zero]

theorem star_N_plus_mul_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * P N_plus = star N_plus := by
  dsimp [P]
  rw [← mul_assoc, star_N_plus_reg N_plus h_reg]

/-- The regular partial-isometry link and its adjoint lie in opposite Peirce
corners: `N₊ = P N₊ Q` and `N₋ = Q N₋ P`. -/
theorem wilson_link_bilateral_corner_support (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * N_plus * Q N_plus = N_plus ∧
    Q N_plus * star N_plus * P N_plus = star N_plus := by
  constructor
  · dsimp [P, Q]
    calc
      (N_plus * star N_plus) * N_plus * (star N_plus * N_plus) =
          (N_plus * star N_plus * N_plus) * (star N_plus * N_plus) := rfl
      _ = N_plus * (star N_plus * N_plus) := by rw [h_reg]
      _ = N_plus := N_plus_mul_Q N_plus h_reg
  · dsimp [P, Q]
    calc
      (star N_plus * N_plus) * star N_plus * (N_plus * star N_plus) =
          (star N_plus * N_plus * star N_plus) * (N_plus * star N_plus) := rfl
      _ = star N_plus * (N_plus * star N_plus) := by
        rw [star_N_plus_reg N_plus h_reg]
      _ = star N_plus := star_N_plus_mul_P N_plus h_reg

/-- The off-diagonal Peirce projection `U_plus_off = P U_+ Q` extracts `N_+`. -/
theorem U_plus_off_eq_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    U_plus_off N_plus = N_plus := by
  have hcorner := wilson_link_bilateral_corner_support N_plus h_reg
  dsimp [U_plus_off, U_plus]
  rw [mul_add, mul_one, add_mul, P_mul_Q N_plus h_nil, hcorner.1, zero_add]

/-- `U_plus_off` also equals the reduced unipotent fluctuation `U_+ - 1`. -/
theorem U_plus_off_eq_U_plus_sub_one (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    U_plus_off N_plus = U_plus N_plus - 1 := by
  rw [U_plus_off_eq_N_plus N_plus h_nil h_reg]
  dsimp [U_plus]
  rw [add_sub_self_left]

/-- The dual off-diagonal Peirce projection `U_minus_off = Q U_- P` extracts `N_-`. -/
theorem U_minus_off_eq_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    U_minus_off N_plus = star N_plus := by
  have hcorner := wilson_link_bilateral_corner_support N_plus h_reg
  dsimp [U_minus_off, U_minus]
  rw [mul_add, mul_one, add_mul, Q_mul_P N_plus h_nil, hcorner.2, zero_add]

/-!
### 3. Main Theorem: ’t Hooft–Wilson Braiding `Z_center * U_plus_off + U_plus_off * Z_center = 0`
-/

/-- Sheet `+` carries `+1` ’t Hooft center charge: `Z_center * P = P`. -/
theorem Z_center_mul_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * P N_plus = P N_plus := by
  dsimp [Z_center]
  calc (P N_plus + P N_plus - 1) * P N_plus
    _ = (P N_plus + P N_plus) * P N_plus - 1 * P N_plus := by rw [sub_mul]
    _ = (P N_plus * P N_plus + P N_plus * P N_plus) - P N_plus := by
        rw [add_mul, one_mul]
    _ = (P N_plus + P N_plus) - P N_plus := by rw [P_idem N_plus h_reg]
    _ = P N_plus := by rw [add_sub_self_right]

/-- Sheet `-` carries `-1` ’t Hooft center charge: `Z_center * Q = -Q`. -/
theorem Z_center_mul_Q (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Z_center N_plus * Q N_plus = -Q N_plus := by
  dsimp [Z_center]
  calc (P N_plus + P N_plus - 1) * Q N_plus
    _ = (P N_plus + P N_plus) * Q N_plus - 1 * Q N_plus := by rw [sub_mul]
    _ = (P N_plus * Q N_plus + P N_plus * Q N_plus) - Q N_plus := by
        rw [add_mul, one_mul]
    _ = (0 + 0) - Q N_plus := by rw [P_mul_Q N_plus h_nil]
    _ = -Q N_plus := by rw [add_zero, zero_sub]

/-- The ’t Hooft disorder loop is a `ℤ₂` involution: `Z_center * Z_center = 1`. -/
theorem Z_center_sq_eq_one (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * Z_center N_plus = 1 := by
  have hP := Z_center_mul_P N_plus h_reg
  calc Z_center N_plus * (P N_plus + P N_plus - 1)
    _ = Z_center N_plus * (P N_plus + P N_plus) - Z_center N_plus * 1 := by rw [mul_sub]
    _ = (Z_center N_plus * P N_plus + Z_center N_plus * P N_plus) - Z_center N_plus := by
        rw [mul_add, mul_one]
    _ = (P N_plus + P N_plus) - ((P N_plus + P N_plus) - 1) := by rw [hP, Z_center]
    _ = ((P N_plus + P N_plus - 1) + 1) - (P N_plus + P N_plus - 1) := by
        rw [sub_add_self (P N_plus + P N_plus) 1]
    _ = 1 := by rw [add_sub_self_left]

/-- On the two-sheet support, the center disorder involution restricts to the
intrinsic flux: `Z_center * V = Σ`. -/
theorem Z_center_mul_V_eq_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * V N_plus = Sigma N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, mul_add, Z_center_mul_P N_plus h_reg,
    Z_center_mul_Q N_plus h_nil, ← sub_eq_add_neg]
  rfl

/-- The support and center disorder operator commute, with the same intrinsic
flux as their product: `V * Z_center = Σ`. -/
theorem V_mul_Z_center_eq_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * Z_center N_plus = Sigma N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  have hP : P N_plus * Z_center N_plus = P N_plus := by
    dsimp [Z_center]
    rw [mul_sub, mul_add, mul_one, P_idem N_plus h_reg]
    exact add_sub_self_right (P N_plus) (P N_plus)
  have hQ : Q N_plus * Z_center N_plus = -Q N_plus := by
    dsimp [Z_center]
    calc Q N_plus * (P N_plus + P N_plus - 1) =
        (Q N_plus * P N_plus + Q N_plus * P N_plus) - Q N_plus := by
          rw [mul_sub, mul_add, mul_one]
      _ = -Q N_plus := by
          rw [Q_mul_P N_plus h_nil]
          simp
  rw [hV, add_mul, hP, hQ, ← sub_eq_add_neg]
  rfl

/-- Left action of `Z_center` on `N_plus`: `Z_center * N_+ = +N_+`. -/
theorem Z_center_mul_N_plus (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * N_plus = N_plus := by
  dsimp [Z_center]
  calc (P N_plus + P N_plus - 1) * N_plus
    _ = (P N_plus + P N_plus) * N_plus - 1 * N_plus := by rw [sub_mul]
    _ = (P N_plus * N_plus + P N_plus * N_plus) - N_plus := by rw [add_mul, one_mul]
    _ = (N_plus + N_plus) - N_plus := by
      simp only [P]
      rw [h_reg]
    _ = N_plus := by rw [add_sub_self_right]

/-- Right action of `Z_center` on `N_plus`: `N_+ * Z_center = -N_+`. -/
theorem N_plus_mul_Z_center (N_plus : B)
    (h_nil : N_plus * N_plus = 0) :
    N_plus * Z_center N_plus = -N_plus := by
  dsimp [Z_center]
  calc N_plus * (P N_plus + P N_plus - 1)
    _ = N_plus * (P N_plus + P N_plus) - N_plus * 1 := by rw [mul_sub]
    _ = (N_plus * P N_plus + N_plus * P N_plus) - N_plus := by rw [mul_add, mul_one]
    _ = (0 + 0) - N_plus := by rw [N_plus_mul_P N_plus h_nil]
    _ = -N_plus := by rw [add_zero, zero_sub]

/-- Left action of `Z_center` on `U_plus_off`: `Z_center * U_plus_off = +U_plus_off`. -/
theorem Z_center_mul_U_plus_off (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * U_plus_off N_plus = U_plus_off N_plus := by
  rw [U_plus_off_eq_N_plus N_plus h_nil h_reg, Z_center_mul_N_plus N_plus h_reg]

/-- Right action of `Z_center` on `U_plus_off`: `U_plus_off * Z_center = -U_plus_off`. -/
theorem U_plus_off_mul_Z_center (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    U_plus_off N_plus * Z_center N_plus = -U_plus_off N_plus := by
  rw [U_plus_off_eq_N_plus N_plus h_nil h_reg, N_plus_mul_Z_center N_plus h_nil]

/-- **Main Theorem (’t Hooft Disorder Loop and Wilson Loop Braiding Relation):**
    Across the two-sheeted vortex condensate, the ’t Hooft disorder operator `Z_center`
    and the off-diagonal Wilson link `U_plus_off` strictly anticommute:
    `Z_center * U_plus_off + U_plus_off * Z_center = 0`. -/
theorem Z_center_braid_U_plus_off (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * U_plus_off N_plus + U_plus_off N_plus * Z_center N_plus = 0 := by
  rw [Z_center_mul_U_plus_off N_plus h_nil h_reg,
      U_plus_off_mul_Z_center N_plus h_nil h_reg,
      ← sub_eq_add_neg, sub_self]

/-- Left action of `Z_center` on `star N_plus`: `Z_center * N_- = -N_-`. -/
theorem Z_center_mul_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0) :
    Z_center N_plus * star N_plus = -star N_plus := by
  dsimp [Z_center]
  calc (P N_plus + P N_plus - 1) * star N_plus
    _ = (P N_plus + P N_plus) * star N_plus - 1 * star N_plus := by rw [sub_mul]
    _ = (P N_plus * star N_plus + P N_plus * star N_plus) - star N_plus := by
        rw [add_mul, one_mul]
    _ = (0 + 0) - star N_plus := by rw [P_mul_star_N_plus N_plus h_nil]
    _ = -star N_plus := by rw [add_zero, zero_sub]

/-- Right action of `Z_center` on `star N_plus`: `N_- * Z_center = +N_-`. -/
theorem star_N_plus_mul_Z_center (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * Z_center N_plus = star N_plus := by
  dsimp [Z_center]
  calc star N_plus * (P N_plus + P N_plus - 1)
    _ = star N_plus * (P N_plus + P N_plus) - star N_plus * 1 := by rw [mul_sub]
    _ = (star N_plus * P N_plus + star N_plus * P N_plus) - star N_plus := by
        rw [mul_add, mul_one]
    _ = (star N_plus + star N_plus) - star N_plus := by
        rw [star_N_plus_mul_P N_plus h_reg]
    _ = star N_plus := by rw [add_sub_self_right]

/-- **Dual ’t Hooft–Wilson Braiding Relation on `U_minus_off`:**
    `Z_center * U_minus_off + U_minus_off * Z_center = 0`. -/
theorem Z_center_braid_U_minus_off (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * U_minus_off N_plus + U_minus_off N_plus * Z_center N_plus = 0 := by
  rw [U_minus_off_eq_star_N_plus N_plus h_nil h_reg,
      Z_center_mul_star_N_plus N_plus h_nil,
      star_N_plus_mul_Z_center N_plus h_reg,
      add_comm (-star N_plus) (star N_plus),
      ← sub_eq_add_neg, sub_self]

/-- **Intrinsic Magnetic Flux Braiding (`Σ * U_plus_off + U_plus_off * Σ = 0`):**
    On the active condensate `V = P + Q`, the magnetic flux `Σ = P - Q` obeys the
    exact same anticommutation braiding with `U_plus_off`. -/
theorem Sigma_braid_U_plus_off (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * U_plus_off N_plus + U_plus_off N_plus * Sigma N_plus = 0 := by
  rw [U_plus_off_eq_N_plus N_plus h_nil h_reg]
  have hL : Sigma N_plus * N_plus = N_plus := by
    dsimp [Sigma]
    rw [sub_mul, h_reg, mul_assoc (star N_plus) N_plus N_plus, h_nil, mul_zero, sub_zero]
  have hR : N_plus * Sigma N_plus = -N_plus := by
    dsimp [Sigma]
    rw [mul_sub, ← mul_assoc N_plus N_plus (star N_plus), h_nil, zero_mul,
        ← mul_assoc N_plus (star N_plus) N_plus, h_reg, zero_sub]
  rw [hL, hR, ← sub_eq_add_neg, sub_self]

/-!
### 4. Group-Level ’t Hooft–Wilson Inversion & Condensate Precipitation
-/

theorem Z_center_conj_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * N_plus * Z_center N_plus = -N_plus := by
  rw [Z_center_mul_N_plus N_plus h_reg, N_plus_mul_Z_center N_plus h_nil]

theorem Z_center_conj_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * star N_plus * Z_center N_plus = -star N_plus := by
  rw [Z_center_mul_star_N_plus N_plus h_nil,
      neg_mul, star_N_plus_mul_Z_center N_plus h_reg]

/-- **Group-Level ’t Hooft–Wilson Inversion I (`Z_center U_+ Z_center = U_+⁻¹`):**
    Conjugating the unipotent Wilson holonomy `U_+ = 1 + N_+` by the ’t Hooft
    disorder loop `Z_center` inverts it to `U_+⁻¹ = 1 - N_+`. -/
theorem Z_center_conj_U_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * U_plus N_plus * Z_center N_plus = U_plus_inv N_plus := by
  dsimp [U_plus, U_plus_inv]
  calc Z_center N_plus * (1 + N_plus) * Z_center N_plus
    _ = (Z_center N_plus * 1 + Z_center N_plus * N_plus) * Z_center N_plus := by
        rw [mul_add]
    _ = Z_center N_plus * Z_center N_plus +
        (Z_center N_plus * N_plus * Z_center N_plus) := by
        rw [mul_one, add_mul]
    _ = 1 + -N_plus := by
        rw [Z_center_sq_eq_one N_plus h_reg, Z_center_conj_N_plus N_plus h_nil h_reg]
    _ = 1 - N_plus := by rw [← sub_eq_add_neg]

/-- **Group-Level ’t Hooft–Wilson Inversion II (`Z_center U_- Z_center = U_-⁻¹`):**
    Conjugating `U_- = 1 + N_-` by `Z_center` inverts it to `U_-⁻¹ = 1 - N_-`. -/
theorem Z_center_conj_U_minus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * U_minus N_plus * Z_center N_plus = U_minus_inv N_plus := by
  dsimp [U_minus, U_minus_inv]
  calc Z_center N_plus * (1 + star N_plus) * Z_center N_plus
    _ = (Z_center N_plus * 1 + Z_center N_plus * star N_plus) * Z_center N_plus := by
        rw [mul_add]
    _ = Z_center N_plus * Z_center N_plus +
        (Z_center N_plus * star N_plus * Z_center N_plus) := by
        rw [mul_one, add_mul]
    _ = 1 + -star N_plus := by
        rw [Z_center_sq_eq_one N_plus h_reg, Z_center_conj_star_N_plus N_plus h_nil h_reg]
    _ = 1 - star N_plus := by rw [← sub_eq_add_neg]

/-- The reduced Sheet `+` Wilson loop holonomy `W_+ = U_+ U_- - 1`. -/
def W_wilson_plus (N_plus : B) : B := U_plus N_plus * U_minus N_plus - 1

theorem W_wilson_plus_eq (N_plus : B) :
    W_wilson_plus N_plus = P N_plus + Phi N_plus := by
  dsimp [W_wilson_plus, U_plus, U_minus, P, Phi]
  calc (1 + N_plus) * (1 + star N_plus) - 1
    _ = ((1 + N_plus) * 1 + (1 + N_plus) * star N_plus) - 1 := by rw [mul_add]
    _ = ((1 + N_plus) + (1 * star N_plus + N_plus * star N_plus)) - 1 := by
        rw [mul_one, add_mul]
    _ = ((1 + N_plus) + (star N_plus + N_plus * star N_plus)) - 1 := by rw [one_mul]
    _ = (((1 + N_plus) + star N_plus) + N_plus * star N_plus) - 1 := by
        rw [← add_assoc (1 + N_plus) (star N_plus)]
    _ = ((1 + (N_plus + star N_plus)) + N_plus * star N_plus) - 1 := by
        rw [add_assoc 1 N_plus (star N_plus)]
    _ = (N_plus * star N_plus + (1 + (N_plus + star N_plus))) - 1 := by
        rw [add_comm (1 + (N_plus + star N_plus))]
    _ = (N_plus * star N_plus + ((N_plus + star N_plus) + 1)) - 1 := by
        rw [add_comm 1 (N_plus + star N_plus)]
    _ = ((N_plus * star N_plus + (N_plus + star N_plus)) + 1) - 1 := by
        rw [← add_assoc (N_plus * star N_plus) (N_plus + star N_plus) 1]
    _ = N_plus * star N_plus + (N_plus + star N_plus) := by
        rw [add_sub_self_right]

theorem Z_center_conj_P (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * P N_plus * Z_center N_plus = P N_plus := by
  rw [Z_center_mul_P N_plus h_reg]
  dsimp [Z_center]
  calc P N_plus * (P N_plus + P N_plus - 1)
    _ = P N_plus * (P N_plus + P N_plus) - P N_plus * 1 := by rw [mul_sub]
    _ = (P N_plus * P N_plus + P N_plus * P N_plus) - P N_plus := by
        rw [mul_add, mul_one]
    _ = (P N_plus + P N_plus) - P N_plus := by rw [P_idem N_plus h_reg]
    _ = P N_plus := by rw [add_sub_self_right]

theorem Z_center_conj_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * Phi N_plus * Z_center N_plus = -Phi N_plus := by
  dsimp [Phi]
  calc Z_center N_plus * (N_plus + star N_plus) * Z_center N_plus
    _ = (Z_center N_plus * N_plus + Z_center N_plus * star N_plus) * Z_center N_plus := by
        rw [mul_add]
    _ = Z_center N_plus * N_plus * Z_center N_plus +
        Z_center N_plus * star N_plus * Z_center N_plus := by rw [add_mul]
    _ = -N_plus + -star N_plus := by
        rw [Z_center_conj_N_plus N_plus h_nil h_reg,
            Z_center_conj_star_N_plus N_plus h_nil h_reg]
    _ = -(N_plus + star N_plus) := by
        rw [neg_add_rev, add_comm (-star N_plus) (-N_plus)]

/-- Conjugating the reduced Wilson loop `W_+` by `Z_center` flips the gauge mode `Φ`:
    `Z_center W_+ Z_center = P - Φ`. -/
theorem Z_center_conj_W_wilson_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_center N_plus * W_wilson_plus N_plus * Z_center N_plus =
      P N_plus - Phi N_plus := by
  rw [W_wilson_plus_eq]
  calc Z_center N_plus * (P N_plus + Phi N_plus) * Z_center N_plus
    _ = (Z_center N_plus * P N_plus + Z_center N_plus * Phi N_plus) * Z_center N_plus := by
        rw [mul_add]
    _ = Z_center N_plus * P N_plus * Z_center N_plus +
        Z_center N_plus * Phi N_plus * Z_center N_plus := by rw [add_mul]
    _ = P N_plus + -Phi N_plus := by
        rw [Z_center_conj_P N_plus h_reg, Z_center_conj_Phi N_plus h_nil h_reg]
    _ = P N_plus - Phi N_plus := by rw [← sub_eq_add_neg]

/-- **’t Hooft–Wilson Orbit Sum (`W_+ + Z_center W_+ Z_center = 2P`):**
    Summing the Wilson loop `W_+` with its ’t Hooft-braided partner eliminates `Φ`
    and precipitates the Sheet `+` condensate `2P`. -/
theorem wilson_thooft_condensate_sum (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_wilson_plus N_plus + Z_center N_plus * W_wilson_plus N_plus * Z_center N_plus =
      P N_plus + P N_plus := by
  rw [Z_center_conj_W_wilson_plus N_plus h_nil h_reg, W_wilson_plus_eq]
  exact add_add_sub_cancel (P N_plus) (Phi N_plus)

/-- **’t Hooft–Wilson Braiding Defect (`W_+ - Z_center W_+ Z_center = 2Φ`):**
    The difference between `W_+` and its ’t Hooft-braided partner isolates twice
    the massive Dirac/gluon vector field `Φ`. -/
theorem wilson_thooft_braiding_defect (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_wilson_plus N_plus - Z_center N_plus * W_wilson_plus N_plus * Z_center N_plus =
      Phi N_plus + Phi N_plus := by
  rw [Z_center_conj_W_wilson_plus N_plus h_nil h_reg, W_wilson_plus_eq]
  exact sub_add_sub_cancel_two (P N_plus) (Phi N_plus)

/-!
### 5. Core-to-Vacuum Boundary Braiding for `Z_vortex = 1 - 2V`
-/

/-- A boundary Wilson link `W_edge(X) = V X (1 - V)` tunneling from the exterior
    vacuum `1 - V` into the two-sheeted vortex core `V`. -/
def W_edge (N_plus X : B) : B := V N_plus * X * (1 - V N_plus)

theorem V_idem (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * V N_plus = V N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV]
  calc (P N_plus + Q N_plus) * (P N_plus + Q N_plus)
    _ = (P N_plus + Q N_plus) * P N_plus + (P N_plus + Q N_plus) * Q N_plus := by
        rw [mul_add]
    _ = (P N_plus * P N_plus + Q N_plus * P N_plus) +
        (P N_plus * Q N_plus + Q N_plus * Q N_plus) := by
        rw [add_mul, add_mul]
    _ = (P N_plus + 0) + (0 + Q N_plus) := by
        rw [P_idem N_plus h_reg, Q_mul_P N_plus h_nil,
            P_mul_Q N_plus h_nil, Q_idem N_plus h_reg]
    _ = P N_plus + Q N_plus := by rw [add_zero, zero_add]

/-- The vortex core/vacuum monodromy is a `ℤ₂` involution whenever the
two-sheet support is idempotent. -/
theorem Z_vortex_sq_eq_one (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_vortex N_plus * Z_vortex N_plus = 1 := by
  dsimp [Z_vortex]
  noncomm_ring [V_idem N_plus h_nil h_reg]

/-- The vortex monodromy assigns charge `-1` to its core support. -/
theorem Z_vortex_mul_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_vortex N_plus * V N_plus = -V N_plus := by
  dsimp [Z_vortex]
  noncomm_ring [V_idem N_plus h_nil h_reg]

/-- The vortex monodromy assigns charge `+1` to the exterior complement. -/
theorem Z_vortex_mul_complement (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_vortex N_plus * (1 - V N_plus) = 1 - V N_plus := by
  dsimp [Z_vortex]
  noncomm_ring [V_idem N_plus h_nil h_reg]

/-- **Vortex Boundary Braiding Theorem (`Z_vortex * W_edge + W_edge * Z_vortex = 0`):**
    Any Wilson link `W_edge(X) = V X (1 - V)` crossing the vortex core boundary
    strictly anticommutes with the Steinberg vortex monodromy `Z_vortex = 1 - 2V`. -/
theorem Z_vortex_braid_W_edge (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Z_vortex N_plus * W_edge N_plus X + W_edge N_plus X * Z_vortex N_plus = 0 := by
  have hVW : V N_plus * W_edge N_plus X = W_edge N_plus X := by
    dsimp [W_edge]
    rw [← mul_assoc (V N_plus) (V N_plus * X) (1 - V N_plus),
        ← mul_assoc (V N_plus) (V N_plus) X,
        V_idem N_plus h_nil h_reg]
  have hWV : W_edge N_plus X * V N_plus = 0 := by
    dsimp [W_edge]
    calc (V N_plus * X * (1 - V N_plus)) * V N_plus
      _ = (V N_plus * X) * ((1 - V N_plus) * V N_plus) := by
          rw [mul_assoc (V N_plus * X) (1 - V N_plus) (V N_plus)]
      _ = (V N_plus * X) * (1 * V N_plus - V N_plus * V N_plus) := by
          rw [sub_mul]
      _ = (V N_plus * X) * (V N_plus - V N_plus) := by
          rw [one_mul, V_idem N_plus h_nil h_reg]
      _ = 0 := by rw [sub_self, mul_zero]
  have hL : Z_vortex N_plus * W_edge N_plus X = -W_edge N_plus X := by
    dsimp [Z_vortex]
    rw [sub_mul, one_mul, add_mul, hVW, sub_add_eq_sub_sub, sub_self, zero_sub]
  have hR : W_edge N_plus X * Z_vortex N_plus = W_edge N_plus X := by
    dsimp [Z_vortex]
    rw [mul_sub, mul_one, mul_add, hWV, add_zero, sub_zero]
  rw [hL, hR, add_comm (-W_edge N_plus X) (W_edge N_plus X),
      ← sub_eq_add_neg, sub_self]

end OperatorAlgebra.PeirceSpine.YangMillsTHooftWilsonBraiding
