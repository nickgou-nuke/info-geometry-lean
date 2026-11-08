/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Abel

namespace OperatorAlgebra.PeirceSpine.RealBdGKreinChiralIdealBridge

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
private theorem add_sub_assoc' (a b c : B) : a + (b - c) = (a + b) - c := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc]

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

/-!
### 1. Chiral Nilpotent & Peirce Ideal Carriers (`BDG₁–BDG₂`)
-/

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- Positive chiral Peirce idempotent `P = N_+ N_-` (Sheet `+` carrier). -/
def P (N_plus : B) : B := N_plus * star N_plus

/-- Negative chiral Peirce idempotent `Q = N_- N_+` (Sheet `-` carrier). -/
def Q (N_plus : B) : B := star N_plus * N_plus

/-- Emergent Real BdG / Krein gap support `V = {N_+, N_-} = P + Q`. -/
def V (N_plus : B) : B := N_plus * star N_plus + star N_plus * N_plus

/-- Intrinsic chiral / particle-hole grading `Σ = [N_+, N_-] = P - Q`. -/
def Sigma (N_plus : B) : B := N_plus * star N_plus - star N_plus * N_plus

/-- Global Krein fundamental involution `S_P = 2P - 1`. -/
def S_P (N_plus : B) : B := P N_plus + P N_plus - 1

/-- Real BdG symmetric pairing operator `Φ = N_+ + N_-`. -/
def Phi (N_plus : B) : B := N_plus + star N_plus

/-- Real BdG skew-symmetric rotor `J = N_+ - N_-`. -/
def J (N_plus : B) : B := N_plus - star N_plus

theorem star_N_plus_sq (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    star N_plus * star N_plus = 0 := by
  rw [← star_mul, h_nil, star_zero]

theorem star_N_plus_reg (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * N_plus * star N_plus = star N_plus := by
  have h := congrArg star h_reg
  rw [star_mul, star_mul, star_star, ← mul_assoc] at h
  exact h

/-- `BDG₁` Mutual Left-Ideal Carrier Equivalence (Sheet `+`):
    Right-multiplying any element `X * N_+` of the nilpotent left ideal `B N_+` by `N_-`
    projects onto `X * P`, and right-multiplying `X * P` by `N_+` recovers `X * N_+`. -/
theorem left_ideal_carrier_plus_to_P (N_plus X : B) :
    (X * N_plus) * star N_plus = X * P N_plus := by
  dsimp [P]
  rw [mul_assoc]

theorem left_ideal_carrier_P_to_plus (N_plus X : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    (X * P N_plus) * N_plus = X * N_plus := by
  dsimp [P]
  rw [mul_assoc X (N_plus * star N_plus) N_plus, h_reg]

/-- `BDG₁` Mutual Left-Ideal Carrier Equivalence (Sheet `-`):
    Right-multiplying `X * N_-` by `N_+` projects onto `X * Q`, and right-multiplying
    `X * Q` by `N_-` recovers `X * N_-`. -/
theorem left_ideal_carrier_minus_to_Q (N_plus X : B) :
    (X * star N_plus) * N_plus = X * Q N_plus := by
  dsimp [Q]
  rw [mul_assoc]

theorem left_ideal_carrier_Q_to_minus (N_plus X : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    (X * Q N_plus) * star N_plus = X * star N_plus := by
  dsimp [Q]
  rw [mul_assoc X (star N_plus * N_plus) (star N_plus), star_N_plus_reg N_plus h_reg]

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

theorem P_star (N_plus : B) : star (P N_plus) = P N_plus := by
  dsimp [P]; rw [star_mul, star_star]

theorem Q_star (N_plus : B) : star (Q N_plus) = Q N_plus := by
  dsimp [Q]; rw [star_mul, star_star]

theorem V_star (N_plus : B) : star (V N_plus) = V N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, star_add, P_star, Q_star]

theorem J_star (N_plus : B) : star (J N_plus) = -J N_plus := by
  dsimp [J]; rw [star_sub, star_star, neg_sub]

theorem P_mul_N_plus (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * N_plus = N_plus := h_reg

theorem N_plus_mul_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    N_plus * P N_plus = 0 := by
  dsimp [P]; rw [← mul_assoc, h_nil, zero_mul]

theorem N_plus_mul_Q (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    N_plus * Q N_plus = N_plus := by
  dsimp [Q]; rw [← mul_assoc, h_reg]

theorem Q_mul_N_plus (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Q N_plus * N_plus = 0 := by
  dsimp [Q]; rw [mul_assoc, h_nil, mul_zero]

theorem P_mul_star_N_plus (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    P N_plus * star N_plus = 0 := by
  dsimp [P]; rw [mul_assoc, star_N_plus_sq N_plus h_nil, mul_zero]

theorem star_N_plus_mul_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * P N_plus = star N_plus := by
  dsimp [P]; rw [← mul_assoc, star_N_plus_reg N_plus h_reg]

theorem Q_mul_star_N_plus (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Q N_plus * star N_plus = star N_plus :=
  star_N_plus_reg N_plus h_reg

theorem star_N_plus_mul_Q (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    star N_plus * Q N_plus = 0 := by
  dsimp [Q]; rw [← mul_assoc, star_N_plus_sq N_plus h_nil, zero_mul]

/-!
### 2. Real BdG / Krein Particle–Hole Algebra & Emergent Spectral Gap (`BDG₃–BDG₅`)
-/

theorem S_P_mul_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    S_P N_plus * P N_plus = P N_plus := by
  dsimp [S_P]
  calc (P N_plus + P N_plus - 1) * P N_plus
    _ = (P N_plus + P N_plus) * P N_plus - 1 * P N_plus := by rw [sub_mul]
    _ = (P N_plus * P N_plus + P N_plus * P N_plus) - P N_plus := by
        rw [add_mul, one_mul]
    _ = (P N_plus + P N_plus) - P N_plus := by rw [P_idem N_plus h_reg]
    _ = P N_plus := by rw [add_sub_self_right]

theorem P_mul_S_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * S_P N_plus = P N_plus := by
  dsimp [S_P]
  calc P N_plus * (P N_plus + P N_plus - 1)
    _ = P N_plus * (P N_plus + P N_plus) - P N_plus * 1 := by rw [mul_sub]
    _ = (P N_plus * P N_plus + P N_plus * P N_plus) - P N_plus := by
        rw [mul_add, mul_one]
    _ = (P N_plus + P N_plus) - P N_plus := by rw [P_idem N_plus h_reg]
    _ = P N_plus := by rw [add_sub_self_right]

theorem S_P_mul_Q (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    S_P N_plus * Q N_plus = -Q N_plus := by
  dsimp [S_P]
  calc (P N_plus + P N_plus - 1) * Q N_plus
    _ = (P N_plus + P N_plus) * Q N_plus - 1 * Q N_plus := by rw [sub_mul]
    _ = (P N_plus * Q N_plus + P N_plus * Q N_plus) - Q N_plus := by
        rw [add_mul, one_mul]
    _ = (0 + 0) - Q N_plus := by rw [P_mul_Q N_plus h_nil]
    _ = -Q N_plus := by rw [add_zero, zero_sub]

theorem Q_mul_S_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Q N_plus * S_P N_plus = -Q N_plus := by
  dsimp [S_P]
  calc Q N_plus * (P N_plus + P N_plus - 1)
    _ = Q N_plus * (P N_plus + P N_plus) - Q N_plus * 1 := by rw [mul_sub]
    _ = (Q N_plus * P N_plus + Q N_plus * P N_plus) - Q N_plus := by
        rw [mul_add, mul_one]
    _ = (0 + 0) - Q N_plus := by rw [Q_mul_P N_plus h_nil]
    _ = -Q N_plus := by rw [add_zero, zero_sub]

theorem S_P_sq_eq_one (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    S_P N_plus * S_P N_plus = 1 := by
  have hP := S_P_mul_P N_plus h_reg
  calc S_P N_plus * (P N_plus + P N_plus - 1)
    _ = S_P N_plus * (P N_plus + P N_plus) - S_P N_plus * 1 := by rw [mul_sub]
    _ = (S_P N_plus * P N_plus + S_P N_plus * P N_plus) - S_P N_plus := by
        rw [mul_add, mul_one]
    _ = (P N_plus + P N_plus) - ((P N_plus + P N_plus) - 1) := by rw [hP, S_P]
    _ = ((P N_plus + P N_plus - 1) + 1) - (P N_plus + P N_plus - 1) := by
        rw [sub_add_self (P N_plus + P N_plus) 1]
    _ = 1 := by rw [add_sub_self_left]

theorem S_P_mul_N_plus (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    S_P N_plus * N_plus = N_plus := by
  dsimp [S_P]
  rw [sub_mul, add_mul, one_mul, P_mul_N_plus N_plus h_reg, add_sub_self_right]

theorem N_plus_mul_S_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    N_plus * S_P N_plus = -N_plus := by
  dsimp [S_P]
  rw [mul_sub, mul_add, mul_one, N_plus_mul_P N_plus h_nil, add_zero, zero_sub]

theorem S_P_mul_star_N_plus (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    S_P N_plus * star N_plus = -star N_plus := by
  dsimp [S_P]
  rw [sub_mul, add_mul, one_mul, P_mul_star_N_plus N_plus h_nil, add_zero, zero_sub]

theorem star_N_plus_mul_S_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * S_P N_plus = star N_plus := by
  dsimp [S_P]
  rw [mul_sub, mul_add, mul_one, star_N_plus_mul_P N_plus h_reg, add_sub_self_right]

/-- **`BDG₃` Krein Rotor Bridge (`S_P * Φ = J` and `Φ * S_P = -J`):**
    Left-multiplying the symmetric BdG pairing `Φ` by the Krein fundamental symmetry `S_P`
    produces the skew-adjoint rotor `J = N_+ - N_-`. -/
theorem S_P_mul_Phi_eq_J (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    S_P N_plus * Phi N_plus = J N_plus := by
  dsimp [Phi, J]
  rw [mul_add, S_P_mul_N_plus N_plus h_reg, S_P_mul_star_N_plus N_plus h_nil,
      ← sub_eq_add_neg]

theorem Phi_mul_S_P_eq_neg_J (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * S_P N_plus = -J N_plus := by
  dsimp [Phi, J]
  rw [add_mul, N_plus_mul_S_P N_plus h_nil, star_N_plus_mul_S_P N_plus h_reg,
      add_comm (-N_plus) (star N_plus), ← sub_eq_add_neg, neg_sub]

/-- **`BDG₄` Real BdG Particle–Hole Anticommutation (`{S_P, Φ} = 0`):**
    The BdG pairing operator `Φ` strictly anticommutes with the Krein grading `S_P`. -/
theorem anticomm_S_P_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (S_P N_plus) (Phi N_plus) = 0 := by
  dsimp [anticomm]
  rw [S_P_mul_Phi_eq_J N_plus h_nil h_reg,
      Phi_mul_S_P_eq_neg_J N_plus h_nil h_reg,
      ← sub_eq_add_neg, sub_self]

/-- **`BDG₅` Emergent Krein / BdG Gap Identity (`S_P * Σ = V` and `Φ² = V`):**
    The Krein gap `V = P + Q` emerges identically from `S_P * Σ` and from `Φ * Φ`. -/
theorem S_P_mul_Sigma_eq_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    S_P N_plus * Sigma N_plus = V N_plus := by
  have hS : Sigma N_plus = P N_plus - Q N_plus := rfl
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hS, hV, mul_sub,
      S_P_mul_P N_plus h_reg, S_P_mul_Q N_plus h_nil,
      sub_eq_add_neg, neg_neg]

theorem Phi_sq_eq_V (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Phi N_plus * Phi N_plus = V N_plus := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  dsimp [Phi, V]
  calc (N_plus + star N_plus) * (N_plus + star N_plus)
    _ = (N_plus + star N_plus) * N_plus + (N_plus + star N_plus) * star N_plus := by
        rw [mul_add]
    _ = (N_plus * N_plus + star N_plus * N_plus) +
        (N_plus * star N_plus + star N_plus * star N_plus) := by
        rw [add_mul, add_mul]
    _ = (0 + star N_plus * N_plus) + (N_plus * star N_plus + 0) := by
        rw [h_nil, h_star_nil]
    _ = star N_plus * N_plus + N_plus * star N_plus := by rw [zero_add, add_zero]
    _ = N_plus * star N_plus + star N_plus * N_plus := by rw [add_comm]

theorem V_mul_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * Phi N_plus = Phi N_plus := by
  have hstarReg := star_N_plus_reg N_plus h_reg
  have hstarNil := star_N_plus_sq N_plus h_nil
  dsimp [V, Phi]
  simp only [add_mul, mul_add]
  rw [h_reg, mul_assoc N_plus (star N_plus) (star N_plus),
    hstarNil, mul_zero, mul_assoc (star N_plus) N_plus N_plus,
    h_nil, mul_zero, hstarReg]
  abel

theorem Sigma_sq_eq_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * Sigma N_plus = V N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  have hS : Sigma N_plus = P N_plus - Q N_plus := rfl
  rw [hS, hV]
  calc (P N_plus - Q N_plus) * (P N_plus - Q N_plus)
      = P N_plus * P N_plus - P N_plus * Q N_plus -
          (Q N_plus * P N_plus - Q N_plus * Q N_plus) := by
            rw [sub_mul, mul_sub, mul_sub]
    _ = P N_plus + Q N_plus := by
      rw [P_idem N_plus h_reg, P_mul_Q N_plus h_nil,
        Q_mul_P N_plus h_nil, Q_idem N_plus h_reg,
        sub_zero, zero_sub]
      abel

theorem V_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * Sigma N_plus = Sigma N_plus := by
  rw [show V N_plus = P N_plus + Q N_plus from rfl,
      show Sigma N_plus = P N_plus - Q N_plus from rfl]
  rw [add_mul, mul_sub, mul_sub,
      P_idem N_plus h_reg, P_mul_Q N_plus h_nil,
      Q_mul_P N_plus h_nil, Q_idem N_plus h_reg]
  abel

theorem Sigma_mul_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * V N_plus = Sigma N_plus := by
  rw [show V N_plus = P N_plus + Q N_plus from rfl,
      show Sigma N_plus = P N_plus - Q N_plus from rfl]
  rw [mul_add, sub_mul, sub_mul,
      P_idem N_plus h_reg, P_mul_Q N_plus h_nil,
      Q_mul_P N_plus h_nil, Q_idem N_plus h_reg]
  abel

theorem J_sq_eq_neg_V (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    J N_plus * J N_plus = -V N_plus := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  dsimp [J, V]
  calc (N_plus - star N_plus) * (N_plus - star N_plus)
    _ = (N_plus - star N_plus) * N_plus - (N_plus - star N_plus) * star N_plus := by
        rw [mul_sub]
    _ = (N_plus * N_plus - star N_plus * N_plus) -
        (N_plus * star N_plus - star N_plus * star N_plus) := by
        rw [sub_mul, sub_mul]
    _ = (0 - star N_plus * N_plus) - (N_plus * star N_plus - 0) := by
        rw [h_nil, h_star_nil]
    _ = -(star N_plus * N_plus) - N_plus * star N_plus := by rw [zero_sub, sub_zero]
    _ = -(star N_plus * N_plus + N_plus * star N_plus) := by
        rw [sub_eq_add_neg, ← neg_add]
    _ = -(N_plus * star N_plus + star N_plus * N_plus) := by
        rw [add_comm (star N_plus * N_plus)]

/-!
### 3. Steinberg–Bogoliubov Unitary & Two-Sheeted Peirce Exchange (`BDG₆–BDG₈`)
-/

def U_plus (N_plus : B) : B := 1 + N_plus
def U_minus_inv (N_plus : B) : B := 1 - star N_plus

/-- The Steinberg–Bogoliubov triple unipotent operator `W_Bog = U_+ U_-⁻¹ U_+`. -/
def W_Bog (N_plus : B) : B :=
  U_plus N_plus * U_minus_inv N_plus * U_plus N_plus

theorem V_mul_P (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * P N_plus = P N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, add_mul, P_idem N_plus h_reg, Q_mul_P N_plus h_nil, add_zero]

theorem P_mul_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * V N_plus = P N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, mul_add, P_idem N_plus h_reg, P_mul_Q N_plus h_nil, add_zero]

theorem V_mul_Q (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * Q N_plus = Q N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, add_mul, P_mul_Q N_plus h_nil, Q_idem N_plus h_reg, zero_add]

theorem Q_mul_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Q N_plus * V N_plus = Q N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, mul_add, Q_mul_P N_plus h_nil, Q_idem N_plus h_reg, zero_add]

theorem V_idem (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * V N_plus = V N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  change V N_plus * (P N_plus + Q N_plus) = P N_plus + Q N_plus
  rw [mul_add, V_mul_P N_plus h_nil h_reg, V_mul_Q N_plus h_nil h_reg]

/-- Algebraic null-cone saturation on the support: this is a ring identity, not
an analytic spectral statement. -/
theorem krein_support_null_cone (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    (V N_plus + Sigma N_plus) * (V N_plus - Sigma N_plus) = 0 := by
  rw [mul_sub, add_mul, add_mul,
    V_idem N_plus h_nil h_reg,
    Sigma_mul_V N_plus h_nil h_reg,
    V_mul_Sigma N_plus h_nil h_reg,
    Sigma_sq_eq_V N_plus h_nil h_reg]
  abel

theorem V_mul_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * N_plus = N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, add_mul, P_mul_N_plus N_plus h_reg, Q_mul_N_plus N_plus h_nil, add_zero]

theorem N_plus_mul_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    N_plus * V N_plus = N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, mul_add, N_plus_mul_P N_plus h_nil, N_plus_mul_Q N_plus h_reg, zero_add]

theorem V_mul_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * star N_plus = star N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, add_mul, P_mul_star_N_plus N_plus h_nil, Q_mul_star_N_plus N_plus h_reg, zero_add]

theorem star_N_plus_mul_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * V N_plus = star N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, mul_add, star_N_plus_mul_P N_plus h_reg, star_N_plus_mul_Q N_plus h_nil, add_zero]

/-- `BDG₆` Algebraic Coagulation of the Steinberg–Bogoliubov Operator:
    `W_Bog = (1 - V) + J`. -/
theorem W_Bog_eq (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus = (1 - V N_plus) + J N_plus := by
  dsimp [W_Bog, U_plus, U_minus_inv, J]
  have h1 : (1 + N_plus) * (1 - star N_plus) =
            (1 + (N_plus - star N_plus)) - P N_plus := by
    dsimp [P]
    calc (1 + N_plus) * (1 - star N_plus)
      _ = (1 + N_plus) * 1 - (1 + N_plus) * star N_plus := by rw [mul_sub]
      _ = (1 + N_plus) - (1 * star N_plus + N_plus * star N_plus) := by
          rw [mul_one, add_mul]
      _ = (1 + N_plus) - (star N_plus + N_plus * star N_plus) := by rw [one_mul]
      _ = ((1 + N_plus) - star N_plus) - N_plus * star N_plus := by
          rw [sub_add_eq_sub_sub]
      _ = (1 + (N_plus - star N_plus)) - N_plus * star N_plus := by
          rw [← add_sub_assoc']
  have hJ_N : (N_plus - star N_plus) * N_plus = -Q N_plus := by
    dsimp [Q]; rw [sub_mul, h_nil, zero_sub]
  have hR : ((1 + (N_plus - star N_plus)) - P N_plus) * N_plus = -Q N_plus := by
    calc ((1 + (N_plus - star N_plus)) - P N_plus) * N_plus
      _ = (1 + (N_plus - star N_plus)) * N_plus - P N_plus * N_plus := by rw [sub_mul]
      _ = (1 * N_plus + (N_plus - star N_plus) * N_plus) - N_plus := by
          rw [add_mul, P_mul_N_plus N_plus h_reg]
      _ = (N_plus + -Q N_plus) - N_plus := by rw [one_mul, hJ_N]
      _ = (-Q N_plus + N_plus) - N_plus := by rw [add_comm N_plus (-Q N_plus)]
      _ = -Q N_plus := by rw [add_sub_self_right]
  rw [h1]
  calc ((1 + (N_plus - star N_plus)) - P N_plus) * (1 + N_plus)
    _ = ((1 + (N_plus - star N_plus)) - P N_plus) * 1 +
        ((1 + (N_plus - star N_plus)) - P N_plus) * N_plus := by rw [mul_add]
    _ = ((1 + (N_plus - star N_plus)) - P N_plus) - Q N_plus := by
        rw [mul_one, hR, ← sub_eq_add_neg]
    _ = (1 + (N_plus - star N_plus)) - (P N_plus + Q N_plus) := by
        rw [← sub_add_eq_sub_sub]
    _ = ((N_plus - star N_plus) + 1) - V N_plus := by
        rw [add_comm 1 (N_plus - star N_plus)]; rfl
    _ = (N_plus - star N_plus) + (1 - V N_plus) := by rw [← add_sub_assoc']
    _ = (1 - V N_plus) + (N_plus - star N_plus) := by rw [add_comm]

theorem star_W_Bog_eq (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star (W_Bog N_plus) = (1 - V N_plus) - J N_plus := by
  rw [W_Bog_eq N_plus h_nil h_reg, star_add, star_sub, star_one,
      V_star, J_star, ← sub_eq_add_neg]

/-- **`BDG₇` Exact Unitarity of the Steinberg–Bogoliubov Operator (`W_Bog * W_Bog* = 1`):**
    The unipotent Bogoliubov braid is strictly unitary in `B`. -/
theorem W_Bog_mul_star_self (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * star (W_Bog N_plus) = 1 := by
  rw [star_W_Bog_eq N_plus h_nil h_reg, W_Bog_eq N_plus h_nil h_reg]
  have h1V_idem : (1 - V N_plus) * (1 - V N_plus) = 1 - V N_plus := by
    rw [mul_sub, mul_one, sub_mul, one_mul, V_idem N_plus h_nil h_reg, sub_self, sub_zero]
  have h1V_J : (1 - V N_plus) * J N_plus = 0 := by
    dsimp [J]
    rw [sub_mul, one_mul, mul_sub,
        V_mul_N_plus N_plus h_nil h_reg,
        V_mul_star_N_plus N_plus h_nil h_reg, sub_self]
  have hJ_1V : J N_plus * (1 - V N_plus) = 0 := by
    dsimp [J]
    rw [mul_sub, mul_one, sub_mul,
        N_plus_mul_V N_plus h_nil h_reg,
        star_N_plus_mul_V N_plus h_nil h_reg, sub_self]
  calc ((1 - V N_plus) + J N_plus) * ((1 - V N_plus) - J N_plus)
    _ = ((1 - V N_plus) + J N_plus) * (1 - V N_plus) -
        ((1 - V N_plus) + J N_plus) * J N_plus := by rw [mul_sub]
    _ = ((1 - V N_plus) * (1 - V N_plus) + J N_plus * (1 - V N_plus)) -
        ((1 - V N_plus) * J N_plus + J N_plus * J N_plus) := by rw [add_mul, add_mul]
    _ = ((1 - V N_plus) + 0) - (0 + -V N_plus) := by
        rw [h1V_idem, hJ_1V, h1V_J, J_sq_eq_neg_V N_plus h_nil]
    _ = (1 - V N_plus) + V N_plus := by
        rw [add_zero, zero_add, sub_eq_add_neg, neg_neg]
    _ = 1 := by rw [sub_add_self]

theorem W_Bog_mul_P (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * P N_plus = -star N_plus := by
  rw [W_Bog_eq N_plus h_nil h_reg, add_mul]
  have h1 : (1 - V N_plus) * P N_plus = 0 := by
    rw [sub_mul, one_mul, V_mul_P N_plus h_nil h_reg, sub_self]
  have h2 : J N_plus * P N_plus = -star N_plus := by
    dsimp [J]
    rw [sub_mul, N_plus_mul_P N_plus h_nil, star_N_plus_mul_P N_plus h_reg, zero_sub]
  rw [h1, h2, zero_add]

theorem W_Bog_mul_Q (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * Q N_plus = N_plus := by
  rw [W_Bog_eq N_plus h_nil h_reg, add_mul]
  have h1 : (1 - V N_plus) * Q N_plus = 0 := by
    rw [sub_mul, one_mul, V_mul_Q N_plus h_nil h_reg, sub_self]
  have h2 : J N_plus * Q N_plus = N_plus := by
    dsimp [J]
    rw [sub_mul, N_plus_mul_Q N_plus h_reg, star_N_plus_mul_Q N_plus h_nil, sub_zero]
  rw [h1, h2, zero_add]

/-- **`BDG₈` Non-Perturbative Sheet Exchange I (`W_Bog * P * W_Bog* = Q`):**
    Conjugating Sheet `+` (`P`) by the Steinberg–Bogoliubov unitary maps it onto Sheet `-` (`Q`). -/
theorem W_Bog_conj_P_eq_Q (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * P N_plus * star (W_Bog N_plus) = Q N_plus := by
  rw [W_Bog_mul_P N_plus h_nil h_reg, star_W_Bog_eq N_plus h_nil h_reg, neg_mul]
  have h1 : star N_plus * (1 - V N_plus) = 0 := by
    rw [mul_sub, mul_one, star_N_plus_mul_V N_plus h_nil h_reg, sub_self]
  have h2 : star N_plus * J N_plus = Q N_plus := by
    dsimp [J, Q]
    rw [mul_sub, star_N_plus_sq N_plus h_nil, sub_zero]
  rw [mul_sub, h1, h2, zero_sub, neg_neg]

/-- **`BDG₈` Non-Perturbative Sheet Exchange II (`W_Bog * Q * W_Bog* = P`):**
    Conjugating Sheet `-` (`Q`) by `W_Bog` maps it onto Sheet `+` (`P`). -/
theorem W_Bog_conj_Q_eq_P (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * Q N_plus * star (W_Bog N_plus) = P N_plus := by
  rw [W_Bog_mul_Q N_plus h_nil h_reg, star_W_Bog_eq N_plus h_nil h_reg]
  have h1 : N_plus * (1 - V N_plus) = 0 := by
    rw [mul_sub, mul_one, N_plus_mul_V N_plus h_nil h_reg, sub_self]
  have h2 : N_plus * J N_plus = -P N_plus := by
    dsimp [J, P]
    rw [mul_sub, h_nil, zero_sub]
  rw [mul_sub, h1, h2, zero_sub, neg_neg]

/-- **`BDG₈` Bogoliubov Inversion of the Chiral Grading (`W_Bog * Σ * W_Bog* = -Σ`):**
    Conjugation by `W_Bog` flips the Krein/chiral grading `Σ = P - Q` to `-Σ = Q - P`. -/
theorem W_Bog_conj_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * Sigma N_plus * star (W_Bog N_plus) = -Sigma N_plus := by
  have hS : Sigma N_plus = P N_plus - Q N_plus := rfl
  rw [hS, mul_sub, sub_mul,
      W_Bog_conj_P_eq_Q N_plus h_nil h_reg,
      W_Bog_conj_Q_eq_P N_plus h_nil h_reg,
      neg_sub]

/-- **`BDG₈` Bogoliubov Invariance of the Spectral Gap (`W_Bog * V * W_Bog* = V`):**
    The emergent BdG/Krein gap `V = P + Q` is invariant under the sheet-exchange unitary. -/
theorem W_Bog_conj_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    W_Bog N_plus * V N_plus * star (W_Bog N_plus) = V N_plus := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  rw [hV, mul_add, add_mul,
      W_Bog_conj_P_eq_Q N_plus h_nil h_reg,
      W_Bog_conj_Q_eq_P N_plus h_nil h_reg,
      add_comm (Q N_plus) (P N_plus)]

/-!
### 4. Emergent Two-Sheeted Peirce Decomposition & Causal Grading as Output (`BDG₉–BDG₁₀`)
-/

/-- The diagonal intra-sheet Peirce projection `D_diag(X) = P X P + Q X Q`. -/
def D_diag (N_plus X : B) : B :=
  P N_plus * X * P N_plus + Q N_plus * X * Q N_plus

/-- The off-diagonal inter-sheet Peirce projection `D_off(X) = P X Q + Q X P`. -/
def D_off (N_plus X : B) : B :=
  P N_plus * X * Q N_plus + Q N_plus * X * P N_plus

/-- **`BDG₉` Emergent Two-Sheeted Peirce Completeness on the Gap Support:**
    Every operator `V X V` on the emergent gap support splits into the intra-sheet
    diagonal sector `D_diag(X)` plus the inter-sheet pairing sector `D_off(X)`. -/
theorem two_sheet_peirce_decomp (N_plus X : B) :
    V N_plus * X * V N_plus = D_diag N_plus X + D_off N_plus X := by
  have hV : V N_plus = P N_plus + Q N_plus := rfl
  dsimp [D_diag, D_off]
  rw [hV]
  calc (P N_plus + Q N_plus) * X * (P N_plus + Q N_plus)
    _ = ((P N_plus + Q N_plus) * X) * P N_plus +
        ((P N_plus + Q N_plus) * X) * Q N_plus := by rw [mul_add]
    _ = (P N_plus * X * P N_plus + Q N_plus * X * P N_plus) +
        (P N_plus * X * Q N_plus + Q N_plus * X * Q N_plus) := by
        rw [add_mul, add_mul, add_mul]
    _ = P N_plus * X * P N_plus +
        (Q N_plus * X * P N_plus + (P N_plus * X * Q N_plus + Q N_plus * X * Q N_plus)) := by
        rw [add_assoc]
    _ = P N_plus * X * P N_plus +
        ((Q N_plus * X * P N_plus + P N_plus * X * Q N_plus) + Q N_plus * X * Q N_plus) := by
        rw [← add_assoc (Q N_plus * X * P N_plus)]
    _ = P N_plus * X * P N_plus +
        (Q N_plus * X * Q N_plus + (P N_plus * X * Q N_plus + Q N_plus * X * P N_plus)) := by
        rw [add_comm (Q N_plus * X * P N_plus + P N_plus * X * Q N_plus),
            add_comm (Q N_plus * X * P N_plus) (P N_plus * X * Q N_plus)]
    _ = (P N_plus * X * P N_plus + Q N_plus * X * Q N_plus) +
        (P N_plus * X * Q N_plus + Q N_plus * X * P N_plus) := by
        rw [← add_assoc]

/-- **`BDG₁₀` Emergent Intra-Sheet Stabilizer (`[S_P, D_diag(X)] = 0`):**
    The diagonal two-sheeted sector commutes with the Krein grading `S_P`. -/
theorem comm_S_P_D_diag (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (S_P N_plus) (D_diag N_plus X) = 0 := by
  dsimp [comm, D_diag]
  have hLP : S_P N_plus * (P N_plus * X * P N_plus) = P N_plus * X * P N_plus := by
    rw [← mul_assoc (S_P N_plus) (P N_plus * X) (P N_plus),
        ← mul_assoc (S_P N_plus) (P N_plus) X,
        S_P_mul_P N_plus h_reg]
  have hRP : (P N_plus * X * P N_plus) * S_P N_plus = P N_plus * X * P N_plus := by
    rw [mul_assoc (P N_plus * X) (P N_plus) (S_P N_plus),
        P_mul_S_P N_plus h_reg]
  have hLQ : S_P N_plus * (Q N_plus * X * Q N_plus) = -(Q N_plus * X * Q N_plus) := by
    rw [← mul_assoc (S_P N_plus) (Q N_plus * X) (Q N_plus),
        ← mul_assoc (S_P N_plus) (Q N_plus) X,
        S_P_mul_Q N_plus h_nil, neg_mul, neg_mul]
  have hRQ : (Q N_plus * X * Q N_plus) * S_P N_plus = -(Q N_plus * X * Q N_plus) := by
    rw [mul_assoc (Q N_plus * X) (Q N_plus) (S_P N_plus),
        Q_mul_S_P N_plus h_nil, mul_neg]
  rw [mul_add, add_mul, hLP, hLQ, hRP, hRQ, sub_self]

/-- **`BDG₁₀` Emergent Inter-Sheet Null Transition (`{S_P, D_off(X)} = 0`):**
    The off-diagonal pairing sector strictly anticommutes with `S_P`. -/
theorem anticomm_S_P_D_off (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (S_P N_plus) (D_off N_plus X) = 0 := by
  dsimp [anticomm, D_off]
  have hLPQ : S_P N_plus * (P N_plus * X * Q N_plus) = P N_plus * X * Q N_plus := by
    rw [← mul_assoc (S_P N_plus) (P N_plus * X) (Q N_plus),
        ← mul_assoc (S_P N_plus) (P N_plus) X,
        S_P_mul_P N_plus h_reg]
  have hRPQ : (P N_plus * X * Q N_plus) * S_P N_plus = -(P N_plus * X * Q N_plus) := by
    rw [mul_assoc (P N_plus * X) (Q N_plus) (S_P N_plus),
        Q_mul_S_P N_plus h_nil, mul_neg]
  have hLQP : S_P N_plus * (Q N_plus * X * P N_plus) = -(Q N_plus * X * P N_plus) := by
    rw [← mul_assoc (S_P N_plus) (Q N_plus * X) (P N_plus),
        ← mul_assoc (S_P N_plus) (Q N_plus) X,
        S_P_mul_Q N_plus h_nil, neg_mul, neg_mul]
  have hRQP : (Q N_plus * X * P N_plus) * S_P N_plus = Q N_plus * X * P N_plus := by
    rw [mul_assoc (Q N_plus * X) (P N_plus) (S_P N_plus),
        P_mul_S_P N_plus h_reg]
  rw [mul_add, add_mul, hLPQ, hLQP, hRPQ, hRQP]
  calc (P N_plus * X * Q N_plus + -(Q N_plus * X * P N_plus)) +
       (-(P N_plus * X * Q N_plus) + Q N_plus * X * P N_plus)
    _ = (P N_plus * X * Q N_plus - Q N_plus * X * P N_plus) -
        (P N_plus * X * Q N_plus - Q N_plus * X * P N_plus) := by
        rw [← sub_eq_add_neg (P N_plus * X * Q N_plus),
            add_comm (-(P N_plus * X * Q N_plus)) (Q N_plus * X * P N_plus),
            ← sub_eq_add_neg (Q N_plus * X * P N_plus),
            ← neg_sub (P N_plus * X * Q N_plus) (Q N_plus * X * P N_plus),
            ← sub_eq_add_neg]
    _ = 0 := by rw [sub_self]

end OperatorAlgebra.PeirceSpine.RealBdGKreinChiralIdealBridge
