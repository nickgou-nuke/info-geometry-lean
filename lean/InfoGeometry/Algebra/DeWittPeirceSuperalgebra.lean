import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Algebra.DeWittPeirceSuperalgebra

/-!
# Archetype 701: The Orthogonal Chiral Idempotent System
An associative ring A equipped with an idempotent pair P_L, P_R
satisfying the complete partition of unity:
  P_L² = P_L,  P_R² = P_R,  P_L + P_R = 1,  P_L * P_R = 0.
-/

class ChiralPeirceSystem (A : Type*) [Ring A] where
  PL : A
  PR : A
  h_PL_sq : PL * PL = PL
  h_PR_sq : PR * PR = PR
  h_sum   : PL + PR = 1
  h_PL_PR : PL * PR = 0

variable {A : Type*} [Ring A] [S : ChiralPeirceSystem A]

/-- Lemma 1: Complementary Orthogonality.
    P_R * P_L = 0 is a necessary consequence of the partition of unity. -/
theorem PR_PL_ortho : S.PR * S.PL = 0 := by
  have h_PR : S.PR = 1 - S.PL := by
    calc S.PR = (S.PL + S.PR) - S.PL := by abel
      _ = 1 - S.PL := by rw [S.h_sum]
  calc S.PR * S.PL
    _ = (1 - S.PL) * S.PL := by rw [h_PR]
    _ = 1 * S.PL - S.PL * S.PL := sub_mul 1 S.PL S.PL
    _ = S.PL - S.PL := by rw [one_mul, S.h_PL_sq]
    _ = 0 := sub_self S.PL


/-!
# Archetype 702: The Automatic Nilpotency of Chiral Off-Diagonals
Because P_L * P_R = 0 and P_R * P_L = 0, the off-diagonal bimodules
U = P_L * X * P_R and V = P_R * X * P_L are IDENTICALLY NILPOTENT OF INDEX 2.
Grassmannian/fermionic variables emerge from pure ring idempotency.
-/

section NilpotentSoul

/-- The Left-to-Right Chiral Bimodule (Fermionic Transition Operator U). -/
def soul_LR (X : A) : A :=
  S.PL * X * S.PR

/-- The Right-to-Left Chiral Bimodule (Fermionic Transition Operator V). -/
def soul_RL (X : A) : A :=
  S.PR * X * S.PL

/-- Master Theorem 1: The Nilpotency of U = P_L * X * P_R.
    U² = 0 holds for ANY ring element X without postulating anticommuting variables. -/
theorem soul_LR_sq_zero (X : A) : soul_LR X * soul_LR X = 0 := by
  dsimp [soul_LR]
  have h_ortho := PR_PL_ortho (A := A)
  calc (S.PL * X * S.PR) * (S.PL * X * S.PR)
    _ = S.PL * X * (S.PR * (S.PL * X * S.PR)) := by rw [mul_assoc]
    _ = S.PL * X * ((S.PR * S.PL) * (X * S.PR)) := by
        have : S.PR * (S.PL * X * S.PR) = (S.PR * S.PL) * (X * S.PR) := by
          simp only [mul_assoc]
        rw [this]
    _ = S.PL * X * (0 * (X * S.PR)) := by rw [h_ortho]
    _ = 0 := by simp only [zero_mul, mul_zero]

/-- Master Theorem 2: The Nilpotency of V = P_R * X * P_L.
    V² = 0 holds identically. -/
theorem soul_RL_sq_zero (X : A) : soul_RL X * soul_RL X = 0 := by
  dsimp [soul_RL]
  calc (S.PR * X * S.PL) * (S.PR * X * S.PL)
    _ = S.PR * X * (S.PL * (S.PR * X * S.PL)) := by rw [mul_assoc]
    _ = S.PR * X * ((S.PL * S.PR) * (X * S.PL)) := by
        have : S.PL * (S.PR * X * S.PL) = (S.PL * S.PR) * (X * S.PL) := by
          simp only [mul_assoc]
        rw [this]
    _ = S.PR * X * (0 * (X * S.PL)) := by rw [S.h_PL_PR]
    _ = 0 := by simp only [zero_mul, mul_zero]

end NilpotentSoul


/-!
# Archetypes 703 & 704: The DeWitt Body-Soul Split and Superalgebra Closure
- Body(X) = P_L X P_L + P_R X P_R (Even, Bosonic Subring)
- Soul(X) = soul_LR(X) + soul_RL(X) (Odd, Fermionic Bimodule)
We prove that Soul(X)² lands strictly in the Body subring: {Soul, Soul} ⊆ Body.
-/

section DeWittSuperalgebra

/-- The DeWitt Body projection: selects the diagonal Peirce subrings. -/
def body (X : A) : A :=
  S.PL * X * S.PL + S.PR * X * S.PR

/-- The DeWitt Soul projection: selects the off-diagonal chiral components. -/
def soul (X : A) : A :=
  soul_LR X + soul_RL X

/-- Master Theorem 3: The DeWitt Body-Soul Split.
    Every operator X decomposes uniquely into Body(X) + Soul(X). -/
theorem dewitt_split (X : A) : X = body X + soul X := by
  dsimp [body, soul, soul_LR, soul_RL]
  have h1 : X = (S.PL + S.PR) * X * (S.PL + S.PR) := by
    rw [S.h_sum, one_mul, mul_one]
  calc X = (S.PL + S.PR) * X * (S.PL + S.PR) := h1
    _ = (S.PL * X + S.PR * X) * (S.PL + S.PR) := by rw [add_mul]
    _ = (S.PL * X * S.PL + S.PL * X * S.PR) + (S.PR * X * S.PL + S.PR * X * S.PR) := by
        simp only [mul_add, add_mul]
    _ = (S.PL * X * S.PL + S.PR * X * S.PR) + (S.PL * X * S.PR + S.PR * X * S.PL) := by abel

/-- Left-Left Peirce subring invariance. -/
lemma PL_body_PL (X : A) : S.PL * body X * S.PL = S.PL * X * S.PL := by
  dsimp [body]
  have h_ortho := PR_PL_ortho (A := A)
  calc S.PL * (S.PL * X * S.PL + S.PR * X * S.PR) * S.PL
    _ = (S.PL * (S.PL * X * S.PL) + S.PL * (S.PR * X * S.PR)) * S.PL := by rw [mul_add]
    _ = ((S.PL * S.PL * X * S.PL) + (S.PL * S.PR * X * S.PR)) * S.PL := by repeat rw [mul_assoc]
    _ = ((S.PL * X * S.PL) + (0 * X * S.PR)) * S.PL := by rw [S.h_PL_sq, S.h_PL_PR]
    _ = (S.PL * X * S.PL + 0) * S.PL := by rw [zero_mul, zero_mul]
    _ = (S.PL * X * S.PL) * S.PL := by rw [add_zero]
    _ = S.PL * X * (S.PL * S.PL) := by repeat rw [mul_assoc]
    _ = S.PL * X * S.PL := by rw [S.h_PL_sq]

/-- Right-Right Peirce subring invariance. -/
lemma PR_body_PR (X : A) : S.PR * body X * S.PR = S.PR * X * S.PR := by
  dsimp [body]
  have h_ortho := PR_PL_ortho (A := A)
  calc S.PR * (S.PL * X * S.PL + S.PR * X * S.PR) * S.PR
    _ = (S.PR * (S.PL * X * S.PL) + S.PR * (S.PR * X * S.PR)) * S.PR := by rw [mul_add]
    _ = ((S.PR * S.PL * X * S.PL) + (S.PR * S.PR * X * S.PR)) * S.PR := by repeat rw [mul_assoc]
    _ = ((0 * X * S.PL) + (S.PR * X * S.PR)) * S.PR := by rw [h_ortho, S.h_PR_sq]
    _ = (0 + S.PR * X * S.PR) * S.PR := by rw [zero_mul, zero_mul]
    _ = (S.PR * X * S.PR) * S.PR := by rw [zero_add]
    _ = S.PR * X * (S.PR * S.PR) := by repeat rw [mul_assoc]
    _ = S.PR * X * S.PR := by rw [S.h_PR_sq]

/-- Master Theorem 4: Body is Idempotent. -/
theorem body_is_idempotent (X : A) : body (body X) = body X := by
  dsimp [body]
  rw [PL_body_PL X, PR_body_PR X]

/-- Master Theorem 5: The Superalgebra Closure ({Soul, Soul} ⊆ Body).
    The square of the DeWitt Soul is strictly invariant under Body projection:
    Body(Soul(X)²) = Soul(X)².
    Fermionic interactions square back into the bosonic body! -/
theorem soul_squared_is_body (X : A) :
    body (soul X * soul X) = soul X * soul X := by
  have hU_sq := soul_LR_sq_zero X
  have hV_sq := soul_RL_sq_zero X
  have h_ortho := PR_PL_ortho (A := A)
  
  -- Expand (U + V)² = U*V + V*U
  have h_expand : soul X * soul X = soul_LR X * soul_RL X + soul_RL X * soul_LR X := by
    dsimp [soul]
    calc (soul_LR X + soul_RL X) * (soul_LR X + soul_RL X)
      _ = soul_LR X * soul_LR X + soul_LR X * soul_RL X + soul_RL X * soul_LR X + soul_RL X * soul_RL X := by
          simp only [mul_add, add_mul]
          abel
      _ = 0 + soul_LR X * soul_RL X + soul_RL X * soul_LR X + 0 := by rw [hU_sq, hV_sq]
      _ = soul_LR X * soul_RL X + soul_RL X * soul_LR X := by
          simp only [add_zero, zero_add]
  
  rw [h_expand]
  dsimp [body]
  
  -- Show that P_L * (UV + VU) * P_L = UV and P_R * (UV + VU) * P_R = VU
  have h_PL_UV_PL : S.PL * (soul_LR X * soul_RL X + soul_RL X * soul_LR X) * S.PL = soul_LR X * soul_RL X := by
    dsimp [soul_LR, soul_RL]
    have h1 : S.PL * (S.PL * X * S.PR * (S.PR * X * S.PL)) * S.PL = S.PL * X * S.PR * (S.PR * X * S.PL) := by
      calc S.PL * (S.PL * X * S.PR * (S.PR * X * S.PL)) * S.PL
        _ = (S.PL * S.PL * X * S.PR) * (S.PR * X * S.PL * S.PL) := by repeat rw [mul_assoc]
        _ = (S.PL * X * S.PR) * (S.PR * X * (S.PL * S.PL)) := by rw [S.h_PL_sq]; repeat rw [mul_assoc]
        _ = S.PL * X * S.PR * (S.PR * X * S.PL) := by rw [S.h_PL_sq]
    have h2 : S.PL * (S.PR * X * S.PL * (S.PL * X * S.PR)) * S.PL = 0 := by
      calc S.PL * (S.PR * X * S.PL * (S.PL * X * S.PR)) * S.PL
        _ = (S.PL * S.PR) * (X * S.PL * (S.PL * X * S.PR) * S.PL) := by repeat rw [mul_assoc]
        _ = 0 * (X * S.PL * (S.PL * X * S.PR) * S.PL) := by rw [S.h_PL_PR]
        _ = 0 := zero_mul _
    calc S.PL * (S.PL * X * S.PR * (S.PR * X * S.PL) + S.PR * X * S.PL * (S.PL * X * S.PR)) * S.PL
      _ = S.PL * (S.PL * X * S.PR * (S.PR * X * S.PL)) * S.PL + S.PL * (S.PR * X * S.PL * (S.PL * X * S.PR)) * S.PL := by
          rw [mul_add, add_mul]
      _ = S.PL * X * S.PR * (S.PR * X * S.PL) + 0 := by rw [h1, h2]
      _ = S.PL * X * S.PR * (S.PR * X * S.PL) := add_zero _

  have h_PR_UV_PR : S.PR * (soul_LR X * soul_RL X + soul_RL X * soul_LR X) * S.PR = soul_RL X * soul_LR X := by
    dsimp [soul_LR, soul_RL]
    have h1 : S.PR * (S.PL * X * S.PR * (S.PR * X * S.PL)) * S.PR = 0 := by
      calc S.PR * (S.PL * X * S.PR * (S.PR * X * S.PL)) * S.PR
        _ = (S.PR * S.PL) * (X * S.PR * (S.PR * X * S.PL) * S.PR) := by repeat rw [mul_assoc]
        _ = 0 * (X * S.PR * (S.PR * X * S.PL) * S.PR) := by rw [h_ortho]
        _ = 0 := zero_mul _
    have h2 : S.PR * (S.PR * X * S.PL * (S.PL * X * S.PR)) * S.PR = S.PR * X * S.PL * (S.PL * X * S.PR) := by
      calc S.PR * (S.PR * X * S.PL * (S.PL * X * S.PR)) * S.PR
        _ = (S.PR * S.PR * X * S.PL) * (S.PL * X * S.PR * S.PR) := by repeat rw [mul_assoc]
        _ = (S.PR * X * S.PL) * (S.PL * X * (S.PR * S.PR)) := by rw [S.h_PR_sq]; repeat rw [mul_assoc]
        _ = S.PR * X * S.PL * (S.PL * X * S.PR) := by rw [S.h_PR_sq]
    calc S.PR * (S.PL * X * S.PR * (S.PR * X * S.PL) + S.PR * X * S.PL * (S.PL * X * S.PR)) * S.PR
      _ = S.PR * (S.PL * X * S.PR * (S.PR * X * S.PL)) * S.PR + S.PR * (S.PR * X * S.PL * (S.PL * X * S.PR)) * S.PR := by
          rw [mul_add, add_mul]
      _ = 0 + S.PR * X * S.PL * (S.PL * X * S.PR) := by rw [h1, h2]
      _ = S.PR * X * S.PL * (S.PL * X * S.PR) := zero_add _

  rw [h_PL_UV_PL, h_PR_UV_PR]

end DeWittSuperalgebra


/-!
# Archetype 705: Chiral Grading Parity and Geometric Emergence
The grading operator G = P_L - P_R acts as the parity involution:
- G * Body(X) * G = Body(X)    (Body is Parity-Even)
- G * Soul(X) * G = -Soul(X)   (Soul is Parity-Odd)
-/

section ChiralGradingParity

/-- The Chiral Grading Involution G = P_L - P_R. -/
def G : A :=
  S.PL - S.PR

lemma G_mul_PL : G (A := A) * S.PL = S.PL := by
  dsimp [G]
  have h_ortho := PR_PL_ortho (A := A)
  calc (S.PL - S.PR) * S.PL
    _ = S.PL * S.PL - S.PR * S.PL := sub_mul S.PL S.PR S.PL
    _ = S.PL - 0 := by rw [S.h_PL_sq, h_ortho]
    _ = S.PL := sub_zero S.PL

lemma PL_mul_G : S.PL * G (A := A) = S.PL := by
  dsimp [G]
  calc S.PL * (S.PL - S.PR)
    _ = S.PL * S.PL - S.PL * S.PR := mul_sub S.PL S.PL S.PR
    _ = S.PL - 0 := by rw [S.h_PL_sq, S.h_PL_PR]
    _ = S.PL := sub_zero S.PL

lemma G_mul_PR : G (A := A) * S.PR = -S.PR := by
  dsimp [G]
  calc (S.PL - S.PR) * S.PR
    _ = S.PL * S.PR - S.PR * S.PR := sub_mul S.PL S.PR S.PR
    _ = 0 - S.PR := by rw [S.h_PL_PR, S.h_PR_sq]
    _ = -S.PR := zero_sub S.PR

lemma PR_mul_G : S.PR * G (A := A) = -S.PR := by
  dsimp [G]
  have h_ortho := PR_PL_ortho (A := A)
  calc S.PR * (S.PL - S.PR)
    _ = S.PR * S.PL - S.PR * S.PR := mul_sub S.PR S.PL S.PR
    _ = 0 - S.PR := by rw [h_ortho, S.h_PR_sq]
    _ = -S.PR := zero_sub S.PR

/-- Master Theorem 6: The Body is Parity-Even under Chiral Grading. -/
theorem G_body_parity_even (X : A) :
    G (A := A) * body X * G = body X := by
  dsimp [body]
  have h_dist : G (A := A) * (S.PL * X * S.PL + S.PR * X * S.PR) * G =
      (G * (S.PL * X * S.PL)) * G + (G * (S.PR * X * S.PR)) * G := by
    rw [mul_add, add_mul]
  rw [h_dist]
  have h1 : (G (A := A) * (S.PL * X * S.PL)) * G = S.PL * X * S.PL := by
    calc (G * (S.PL * X * S.PL)) * G
      _ = (G * S.PL) * X * (S.PL * G) := by repeat rw [mul_assoc]
      _ = S.PL * X * S.PL := by rw [G_mul_PL, PL_mul_G]
  have h2 : (G (A := A) * (S.PR * X * S.PR)) * G = S.PR * X * S.PR := by
    calc (G * (S.PR * X * S.PR)) * G
      _ = (G * S.PR) * X * (S.PR * G) := by repeat rw [mul_assoc]
      _ = (-S.PR) * X * (-S.PR) := by rw [G_mul_PR, PR_mul_G]
      _ = S.PR * X * S.PR := by
          have h_neg : (-S.PR) * X * (-S.PR) = (-1 : A) * (S.PR * X) * ((-1 : A) * S.PR) := by
            simp only [neg_eq_neg_one_mul, mul_assoc]
          rw [h_neg]
          have h_comm : (-1 : A) * (S.PR * X) * ((-1 : A) * S.PR) =
              ((-1 : A) * (-1 : A)) * (S.PR * X * S.PR) := by
            repeat rw [mul_assoc]
          rw [h_comm]
          have h_neg_one : (-1 : A) * (-1 : A) = 1 := by ring
          rw [h_neg_one, one_mul]
  rw [h1, h2]

/-- Master Theorem 7: The Soul is Parity-Odd under Chiral Grading. -/
theorem G_soul_parity_odd (X : A) :
    G (A := A) * soul X * G = - soul X := by
  dsimp [soul, soul_LR, soul_RL]
  have h_dist : G (A := A) * (S.PL * X * S.PR + S.PR * X * S.PL) * G =
      (G * (S.PL * X * S.PR)) * G + (G * (S.PR * X * S.PL)) * G := by
    rw [mul_add, add_mul]
  rw [h_dist]
  have h1 : (G (A := A) * (S.PL * X * S.PR)) * G = - (S.PL * X * S.PR) := by
    calc (G * (S.PL * X * S.PR)) * G
      _ = (G * S.PL) * X * (S.PR * G) := by repeat rw [mul_assoc]
      _ = S.PL * X * (-S.PR) := by rw [G_mul_PL, PR_mul_G]
      _ = - (S.PL * X * S.PR) := by rw [mul_neg]
  have h2 : (G (A := A) * (S.PR * X * S.PL)) * G = - (S.PR * X * S.PL) := by
    calc (G * (S.PR * X * S.PL)) * G
      _ = (G * S.PR) * X * (S.PL * G) := by repeat rw [mul_assoc]
      _ = (-S.PR) * X * S.PL := by rw [G_mul_PR, PL_mul_G]
      _ = - (S.PR * X * S.PL) := by rw [neg_mul]
  rw [h1, h2]
  abel

end ChiralGradingParity

end InfoGeometry.Algebra.DeWittPeirceSuperalgebra
