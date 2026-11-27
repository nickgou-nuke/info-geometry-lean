/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Basic.Real.Basic
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

/-- Constructive non-degenerate two-sheet witness of `ChiralPeirceSystem` on `ℤ × ℤ`. -/
@[instance_reducible]
def prodChiralPeirceSystem : ChiralPeirceSystem (ℤ × ℤ) where
  PL := (1, 0)
  PR := (0, 1)
  h_PL_sq := rfl
  h_PR_sq := rfl
  h_sum := rfl
  h_PL_PR := rfl

theorem prodChiralPeirceSystem_nontrivial :
    prodChiralPeirceSystem.PL ≠ 0 ∧ prodChiralPeirceSystem.PR ≠ 0 ∧
      prodChiralPeirceSystem.PL ≠ prodChiralPeirceSystem.PR := by
  decide

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
    _ = S.PL * X * ((S.PR * S.PL) * (X * S.PR)) := by simp only [mul_assoc]
    _ = S.PL * X * (0 * (X * S.PR)) := by rw [h_ortho]
    _ = 0 := by simp only [zero_mul, mul_zero]

/-- Master Theorem 2: The Nilpotency of V = P_R * X * P_L.
    V² = 0 holds identically. -/
theorem soul_RL_sq_zero (X : A) : soul_RL X * soul_RL X = 0 := by
  dsimp [soul_RL]
  calc (S.PR * X * S.PL) * (S.PR * X * S.PL)
    _ = S.PR * X * (S.PL * (S.PR * X * S.PL)) := by rw [mul_assoc]
    _ = S.PR * X * ((S.PL * S.PR) * (X * S.PL)) := by simp only [mul_assoc]
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

/-- Additivity of the two Peirce soul-corner projections. -/
theorem soul_LR_add (X Y : A) : soul_LR (X + Y) = soul_LR X + soul_LR Y := by
  simp [soul_LR, add_mul, mul_add]

theorem soul_RL_add (X Y : A) : soul_RL (X + Y) = soul_RL X + soul_RL Y := by
  simp [soul_RL, add_mul, mul_add]

/-- Master Theorem 3: The DeWitt Body-Soul Split.
    Every operator X decomposes uniquely into Body(X) + Soul(X). -/
theorem dewitt_split (X : A) : X = body X + soul X := by
  dsimp [body, soul, soul_LR, soul_RL]
  calc X = (S.PL + S.PR) * X * (S.PL + S.PR) := by rw [S.h_sum, one_mul, mul_one]
    _ = (S.PL * X + S.PR * X) * (S.PL + S.PR) := by rw [add_mul]
    _ = (S.PL * X * S.PL + S.PL * X * S.PR) + (S.PR * X * S.PL + S.PR * X * S.PR) := by
        noncomm_ring
    _ = (S.PL * X * S.PL + S.PR * X * S.PR) + (S.PL * X * S.PR + S.PR * X * S.PL) := by
        ac_rfl

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
  change S.PL * body X * S.PL + S.PR * body X * S.PR =
    S.PL * X * S.PL + S.PR * X * S.PR
  rw [PL_body_PL X, PR_body_PR X]

/-- The left-to-right corner projection is idempotent. -/
theorem soul_LR_is_idempotent (X : A) :
    soul_LR (soul_LR X) = soul_LR X := by
  dsimp [soul_LR]
  calc
    S.PL * (S.PL * X * S.PR) * S.PR =
        (S.PL * S.PL) * X * (S.PR * S.PR) := by noncomm_ring
    _ = S.PL * X * S.PR := by rw [S.h_PL_sq, S.h_PR_sq]

/-- The right-to-left corner projection is idempotent. -/
theorem soul_RL_is_idempotent (X : A) :
    soul_RL (soul_RL X) = soul_RL X := by
  dsimp [soul_RL]
  calc
    S.PR * (S.PR * X * S.PL) * S.PL =
        (S.PR * S.PR) * X * (S.PL * S.PL) := by noncomm_ring
    _ = S.PR * X * S.PL := by rw [S.h_PR_sq, S.h_PL_sq]

/-- Opposite Peirce corners annihilate under the soul projections. -/
theorem soul_LR_soul_RL_eq_zero (X : A) :
    soul_LR (soul_RL X) = 0 := by
  dsimp [soul_LR, soul_RL]
  calc
    S.PL * (S.PR * X * S.PL) * S.PR =
        (S.PL * S.PR) * X * (S.PL * S.PR) := by noncomm_ring
    _ = 0 := by rw [S.h_PL_PR]; simp

theorem soul_RL_soul_LR_eq_zero (X : A) :
    soul_RL (soul_LR X) = 0 := by
  dsimp [soul_RL, soul_LR]
  have hPRPL := PR_PL_ortho (A := A)
  calc
    S.PR * (S.PL * X * S.PR) * S.PL =
        (S.PR * S.PL) * X * (S.PR * S.PL) := by noncomm_ring
    _ = 0 := by rw [hPRPL]; simp

/-- The total DeWitt soul is an idempotent linear projection onto the odd
Peirce corners. -/
theorem soul_is_idempotent (X : A) : soul (soul X) = soul X := by
  unfold soul
  rw [soul_LR_add, soul_RL_add, soul_LR_is_idempotent, soul_LR_soul_RL_eq_zero,
    soul_RL_soul_LR_eq_zero, soul_RL_is_idempotent]
  simp

/-- The DeWitt body and soul projections are mutually annihilating.  This is
the ring-general Peirce orthogonality underlying their complementary
idempotence. -/
theorem body_soul_orthogonal (X : A) :
    body (soul X) = 0 ∧ soul (body X) = 0 := by
  have hPRPL := PR_PL_ortho (A := A)
  have h11LR : S.PL * soul_LR X * S.PL = 0 := by
    dsimp [soul_LR]
    calc
      S.PL * (S.PL * X * S.PR) * S.PL =
          (S.PL * S.PL) * X * (S.PR * S.PL) := by noncomm_ring
      _ = 0 := by rw [S.h_PL_sq, hPRPL]; simp
  have h11RL : S.PL * soul_RL X * S.PL = 0 := by
    dsimp [soul_RL]
    calc
      S.PL * (S.PR * X * S.PL) * S.PL =
          (S.PL * S.PR) * X * (S.PL * S.PL) := by noncomm_ring
      _ = 0 := by rw [S.h_PL_PR, S.h_PL_sq]; simp
  have h00LR : S.PR * soul_LR X * S.PR = 0 := by
    dsimp [soul_LR]
    calc
      S.PR * (S.PL * X * S.PR) * S.PR =
          (S.PR * S.PL) * X * (S.PR * S.PR) := by noncomm_ring
      _ = 0 := by rw [hPRPL, S.h_PR_sq]; simp
  have h00RL : S.PR * soul_RL X * S.PR = 0 := by
    dsimp [soul_RL]
    calc
      S.PR * (S.PR * X * S.PL) * S.PR =
          (S.PR * S.PR) * X * (S.PL * S.PR) := by noncomm_ring
      _ = 0 := by rw [S.h_PR_sq, S.h_PL_PR]; simp
  have hLR11 : soul_LR (S.PL * X * S.PL) = 0 := by
    dsimp [soul_LR]
    calc
      S.PL * (S.PL * X * S.PL) * S.PR =
          (S.PL * S.PL) * X * (S.PL * S.PR) := by noncomm_ring
      _ = 0 := by rw [S.h_PL_sq, S.h_PL_PR]; simp
  have hLR00 : soul_LR (S.PR * X * S.PR) = 0 := by
    dsimp [soul_LR]
    calc
      S.PL * (S.PR * X * S.PR) * S.PR =
          (S.PL * S.PR) * X * (S.PR * S.PR) := by noncomm_ring
      _ = 0 := by rw [S.h_PL_PR, S.h_PR_sq]; simp
  have hRL11 : soul_RL (S.PL * X * S.PL) = 0 := by
    dsimp [soul_RL]
    calc
      S.PR * (S.PL * X * S.PL) * S.PL =
          (S.PR * S.PL) * X * (S.PL * S.PL) := by noncomm_ring
      _ = 0 := by rw [hPRPL, S.h_PL_sq]; simp
  have hRL00 : soul_RL (S.PR * X * S.PR) = 0 := by
    dsimp [soul_RL]
    calc
      S.PR * (S.PR * X * S.PR) * S.PL =
          (S.PR * S.PR) * X * (S.PR * S.PL) := by noncomm_ring
      _ = 0 := by rw [S.h_PR_sq, hPRPL]; simp
  constructor
  · change S.PL * (soul_LR X + soul_RL X) * S.PL +
      S.PR * (soul_LR X + soul_RL X) * S.PR = 0
    simp only [mul_add, add_mul, h11LR, h11RL, h00LR, h00RL, add_zero]
  · calc
      soul (body X) =
          soul_LR (S.PL * X * S.PL) + soul_LR (S.PR * X * S.PR) +
            soul_RL (S.PL * X * S.PL) + soul_RL (S.PR * X * S.PR) := by
              unfold soul body
              rw [soul_LR_add, soul_RL_add]
              ac_rfl
      _ = 0 := by rw [hLR11, hLR00, hRL11, hRL00]; simp

/-- The DeWitt body and soul maps are additive projections. -/
theorem body_add (X Y : A) : body (X + Y) = body X + body Y := by
  dsimp [body]
  simp only [mul_add, add_mul]
  abel

theorem soul_add (X Y : A) : soul (X + Y) = soul X + soul Y := by
  unfold soul
  rw [soul_LR_add, soul_RL_add]
  abel

/-- Uniqueness of the DeWitt decomposition in the original noncommutative ring.
If `X = B + F`, with `B` fixed by the body projection and `F` fixed by the
soul projection, then these components must be the canonical projections of
`X`.  No scalar or commutative surrogate is used. -/
theorem dewitt_split_unique (X B F : A) (hX : X = B + F)
    (hB : body B = B) (hF : soul F = F) :
    B = body X ∧ F = soul X := by
  have hBodyF : body F = 0 := by
    calc body F = body (soul F) := by rw [hF]
      _ = 0 := (body_soul_orthogonal F).1
  have hSoulB : soul B = 0 := by
    calc soul B = soul (body B) := by rw [hB]
      _ = 0 := (body_soul_orthogonal B).2
  constructor
  · calc B = body B := hB.symm
      _ = body (B + F) := by rw [body_add, hB, hBodyF, add_zero]
      _ = body X := by rw [hX]
  · calc F = soul F := hF.symm
      _ = soul (B + F) := by rw [soul_add, hSoulB, hF, zero_add]
      _ = soul X := by rw [hX]

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
      simp only [mul_assoc, S.h_PL_sq]
      rw [← mul_assoc, S.h_PL_sq]
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
      simp only [mul_assoc, S.h_PR_sq]
      rw [← mul_assoc, S.h_PR_sq]
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
  have h_neg_mul_neg (x y : A) : (-x) * (-y) = x * y := by
    calc
      (-x) * (-y) = -(x * (-y)) := by rw [neg_mul]
      _ = -(-(x * y)) := by rw [mul_neg]
      _ = x * y := neg_neg _
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
          calc
            (-S.PR) * X * (-S.PR) = - (S.PR * X) * (-S.PR) := by rw [neg_mul]
            _ = S.PR * X * S.PR := h_neg_mul_neg (S.PR * X) S.PR
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
      _ = - (S.PR * X * S.PL) := by
        calc
          (-S.PR) * X * S.PL = -(S.PR * X) * S.PL := by rw [neg_mul]
          _ = -(S.PR * X * S.PL) := by rw [neg_mul]
  rw [h1, h2]
  abel

/-- The left-to-right DeWitt corner is itself odd under the chiral grading. -/
theorem G_soul_LR_parity_odd (X : A) :
    G (A := A) * soul_LR X * G = - soul_LR X := by
  dsimp [soul_LR]
  calc
    G * (S.PL * X * S.PR) * G
        = (G * S.PL) * X * (S.PR * G) := by repeat rw [mul_assoc]
    _ = S.PL * X * (-S.PR) := by rw [G_mul_PL, PR_mul_G]
    _ = -(S.PL * X * S.PR) := by rw [mul_neg]

/-- A left-to-right corner fixed by the chiral grading has additive order
dividing two. This form needs no characteristic or torsion-freeness assumption. -/
theorem G_soul_LR_fixed_two_nsmul_zero (X : A)
    (hfix : G (A := A) * soul_LR X * G = soul_LR X) :
    (2 : ℕ) • soul_LR X = 0 := by
  have hodd := G_soul_LR_parity_odd X
  have hneg : -soul_LR X = soul_LR X := by rw [← hodd, hfix]
  have htwo : soul_LR X + soul_LR X = 0 := by
    calc
      soul_LR X + soul_LR X = -soul_LR X + soul_LR X := by rw [hneg]
      _ = 0 := neg_add_cancel _
  rw [two_nsmul]
  exact htwo

end ChiralGradingParity

/-!
# Higher Grades from Noncommutativity Obstructions

When `P_L` fails to commute with an operator `X`, the commutator `[P_L, X]`
does not vanish or collapse to a scalar: it automatically isolates the odd
bimodule corners (`soul_LR X - soul_RL X`), while the iterated commutator
`[P_L, [P_L, X]]` recovers the total `soul X` without requiring `1/2`.
Similarly, the Halmos obstruction `[P_L, P']` of two noncommuting idempotents
lies purely in the odd `soul`, and its square `[P_L, P']²` drops back into the
even `body` and commutes with both `P_L` and `P'`. Finally, the anticommutation
obstruction between chiral grading `G` and sheet swap `R` (`G * R + R * G = 0`)
generates the grade-2 bivector `G * R` satisfying `(G * R)² = -(R²)` and
anticommuting with both generators.
-/
section NoncommutativityHigherGrades

/-- The ring commutator `[x, y] = x * y - y * x` measuring noncommutativity obstruction. -/
def comm (x y : A) : A := x * y - y * x

private lemma G_mul_G : G (A := A) * G (A := A) = 1 := by
  dsimp [G]
  have h_ortho := PR_PL_ortho (A := A)
  calc (S.PL - S.PR) * (S.PL - S.PR)
    _ = S.PL * S.PL - S.PL * S.PR - (S.PR * S.PL - S.PR * S.PR) := by noncomm_ring
    _ = S.PL - 0 - (0 - S.PR) := by rw [S.h_PL_sq, S.h_PL_PR, h_ortho, S.h_PR_sq]
    _ = S.PL + S.PR := by abel
    _ = 1 := S.h_sum

/-- First-order noncommutativity obstruction with `P_L` isolates the graded chiral soul corners:
`[P_L, X] = soul_LR X - soul_RL X`. -/
theorem comm_PL_eq_soul_LR_sub_soul_RL (X : A) :
    comm S.PL X = soul_LR X - soul_RL X := by
  dsimp [comm, soul_LR, soul_RL]
  calc S.PL * X - X * S.PL
    _ = S.PL * X * (S.PL + S.PR) - (S.PL + S.PR) * X * S.PL := by
        rw [S.h_sum, mul_one, one_mul]
    _ = (S.PL * X * S.PL + S.PL * X * S.PR) - (S.PL * X * S.PL + S.PR * X * S.PL) := by
        noncomm_ring
    _ = S.PL * X * S.PR - S.PR * X * S.PL := by abel

/-- First-order noncommutativity `[P_L, X]` equals the chiral grading applied to the odd soul:
`[P_L, X] = G * soul X`. -/
theorem comm_PL_eq_G_mul_soul (X : A) :
    comm S.PL X = G (A := A) * soul X := by
  rw [comm_PL_eq_soul_LR_sub_soul_RL]
  dsimp [soul, soul_LR, soul_RL]
  calc S.PL * X * S.PR - S.PR * X * S.PL
    _ = S.PL * X * S.PR + (-S.PR) * X * S.PL := by
        rw [neg_mul, neg_mul, ← sub_eq_add_neg]
    _ = (G (A := A) * S.PL) * X * S.PR + (G (A := A) * S.PR) * X * S.PL := by
        rw [G_mul_PL, G_mul_PR]
    _ = G (A := A) * (S.PL * X * S.PR + S.PR * X * S.PL) := by
        rw [mul_add]
        repeat rw [mul_assoc]

/-- Double commutator `[P_L, [P_L, X]]` recovers the total odd `soul X` in any associative ring
without requiring division by `2`. -/
theorem comm_PL_iter_sq_eq_soul (X : A) :
    comm S.PL (comm S.PL X) = soul X := by
  rw [comm_PL_eq_soul_LR_sub_soul_RL X]
  dsimp [comm, soul, soul_LR, soul_RL]
  have h_ortho := PR_PL_ortho (A := A)
  calc S.PL * (S.PL * X * S.PR - S.PR * X * S.PL) -
        (S.PL * X * S.PR - S.PR * X * S.PL) * S.PL
      = ((S.PL * S.PL) * X * S.PR - (S.PL * S.PR) * X * S.PL) -
          (S.PL * X * (S.PR * S.PL) - S.PR * X * (S.PL * S.PL)) := by
          noncomm_ring
    _ = (S.PL * X * S.PR - 0) - (0 - S.PR * X * S.PL) := by
          rw [S.h_PL_sq, S.h_PL_PR, h_ortho]
          simp
    _ = S.PL * X * S.PR + S.PR * X * S.PL := by
          noncomm_ring

/-- Triple commutator `[P_L, [P_L, [P_L, X]]]` stabilizes identically to `[P_L, X]`. -/
theorem comm_PL_iter_cube_eq_comm_PL (X : A) :
    comm S.PL (comm S.PL (comm S.PL X)) = comm S.PL X := by
  have hLR : soul_LR (soul X) = soul_LR X := by
    unfold soul
    rw [soul_LR_add, soul_LR_is_idempotent, soul_LR_soul_RL_eq_zero, add_zero]
  have hRL : soul_RL (soul X) = soul_RL X := by
    unfold soul
    rw [soul_RL_add, soul_RL_soul_LR_eq_zero, soul_RL_is_idempotent, zero_add]
  calc
    comm S.PL (comm S.PL (comm S.PL X)) = comm S.PL (soul X) := by
      rw [comm_PL_iter_sq_eq_soul X]
    _ = soul_LR (soul X) - soul_RL (soul X) :=
      comm_PL_eq_soul_LR_sub_soul_RL (soul X)
    _ = soul_LR X - soul_RL X := by rw [hLR, hRL]
    _ = comm S.PL X := (comm_PL_eq_soul_LR_sub_soul_RL X).symm

/-- `X` commutes with `P_L` if and only if its odd `soul` vanishes. -/
theorem comm_PL_eq_zero_iff_soul_eq_zero (X : A) :
    comm S.PL X = 0 ↔ soul X = 0 := by
  constructor
  · intro h
    calc soul X = comm S.PL (comm S.PL X) := (comm_PL_iter_sq_eq_soul X).symm
      _ = comm S.PL 0 := by rw [h]
      _ = 0 := by simp [comm]
  · intro h
    rw [comm_PL_eq_G_mul_soul, h, mul_zero]

/-- `X` commutes with `P_L` if and only if `X` lies entirely in the even `body`. -/
theorem comm_PL_eq_zero_iff_eq_body (X : A) :
    comm S.PL X = 0 ↔ X = body X := by
  rw [comm_PL_eq_zero_iff_soul_eq_zero]
  constructor
  · intro h
    calc X = body X + soul X := dewitt_split X
      _ = body X + 0 := by rw [h]
      _ = body X := add_zero _
  · intro h
    calc soul X = soul (body X) := by rw [← h]
      _ = 0 := (body_soul_orthogonal X).2

/-- The commutator `[P_L, P']` with any second element `P'` (such as a second idempotent)
lies purely in the odd `soul` (zero `body` projection). -/
theorem two_idempotent_comm_is_pure_soul (P' : A) :
    body (comm S.PL P') = 0 ∧ soul (comm S.PL P') = comm S.PL P' := by
  have h_ortho := PR_PL_ortho (A := A)
  rw [comm_PL_eq_soul_LR_sub_soul_RL]
  constructor
  · dsimp [body, soul_LR, soul_RL]
    calc S.PL * (S.PL * P' * S.PR - S.PR * P' * S.PL) * S.PL +
          S.PR * (S.PL * P' * S.PR - S.PR * P' * S.PL) * S.PR
      _ = ((S.PL * S.PL) * P' * (S.PR * S.PL) - (S.PL * S.PR) * P' * (S.PL * S.PL)) +
            ((S.PR * S.PL) * P' * (S.PR * S.PR) - (S.PR * S.PR) * P' * (S.PL * S.PR)) := by
            noncomm_ring
      _ = ((S.PL * P' * 0) - (0 * P' * S.PL)) + ((0 * P' * S.PR) - (S.PR * P' * 0)) := by
            rw [S.h_PL_sq, S.h_PR_sq, S.h_PL_PR, h_ortho]
      _ = 0 := by simp
  · dsimp [soul, soul_LR, soul_RL]
    calc (S.PL * (S.PL * P' * S.PR - S.PR * P' * S.PL) * S.PR +
            S.PR * (S.PL * P' * S.PR - S.PR * P' * S.PL) * S.PL)
      _ = ((S.PL * S.PL) * P' * (S.PR * S.PR) - (S.PL * S.PR) * P' * (S.PL * S.PR)) +
            ((S.PR * S.PL) * P' * (S.PR * S.PL) - (S.PR * S.PR) * P' * (S.PL * S.PL)) := by
            noncomm_ring
      _ = (S.PL * P' * S.PR - 0 * P' * 0) + (0 * P' * 0 - S.PR * P' * S.PL) := by
            rw [S.h_PL_sq, S.h_PR_sq, S.h_PL_PR, h_ortho]
      _ = S.PL * P' * S.PR - S.PR * P' * S.PL := by
            simp only [zero_mul, mul_zero, sub_zero, zero_sub]
            abel

/-- The Halmos commutator `[P_L, P']` anticommutes with the chiral grading `G`. -/
theorem two_idempotent_comm_anticomm_G (P' : A) :
    G (A := A) * comm S.PL P' = -(comm S.PL P' * G (A := A)) := by
  have hSoul := (two_idempotent_comm_is_pure_soul (A := A) P').2
  have hOdd := G_soul_parity_odd (A := A) (comm S.PL P')
  rw [hSoul] at hOdd
  calc G (A := A) * comm S.PL P'
    _ = (G (A := A) * comm S.PL P') * (G (A := A) * G (A := A)) := by rw [G_mul_G, mul_one]
    _ = (G (A := A) * comm S.PL P' * G (A := A)) * G (A := A) := by simp only [mul_assoc]
    _ = (-comm S.PL P') * G (A := A) := by rw [hOdd]
    _ = -(comm S.PL P' * G (A := A)) := by rw [neg_mul]

/-- The squared commutator `[P_L, P']²` drops back into the even `body` subalgebra. -/
theorem two_idempotent_comm_sq_is_body (P' : A) :
    body (comm S.PL P' * comm S.PL P') = comm S.PL P' * comm S.PL P' := by
  have hSoul := (two_idempotent_comm_is_pure_soul (A := A) P').2
  calc body (comm S.PL P' * comm S.PL P')
    _ = body (soul (comm S.PL P') * soul (comm S.PL P')) := by rw [hSoul]
    _ = soul (comm S.PL P') * soul (comm S.PL P') := soul_squared_is_body (comm S.PL P')
    _ = comm S.PL P' * comm S.PL P' := by rw [hSoul]

/-- The squared commutator `[P_L, P']²` commutes with the first idempotent `P_L`. -/
theorem two_idempotent_comm_sq_comm_PL (P' : A) :
    comm S.PL (comm S.PL P' * comm S.PL P') = 0 :=
  (comm_PL_eq_zero_iff_eq_body _).mpr (two_idempotent_comm_sq_is_body P').symm

/-- For any second idempotent `P'` (`P' * P' = P'`), the squared Halmos obstruction
`[P_L, P']²` also commutes with `P'` (generating central curvature invariants). -/
theorem two_idempotent_comm_sq_comm_second (P' : A) (hP' : P' * P' = P') :
    comm P' (comm S.PL P' * comm S.PL P') = 0 := by
  have h1 : P' * comm S.PL P' = comm S.PL P' * (1 - P') := by
    dsimp [comm]
    calc P' * (S.PL * P' - P' * S.PL)
      _ = P' * S.PL * P' - (P' * P') * S.PL := by noncomm_ring
      _ = P' * S.PL * P' - P' * S.PL := by rw [hP']
      _ = S.PL * P' - S.PL * (P' * P') - P' * S.PL + P' * S.PL * P' := by rw [hP']; abel
      _ = (S.PL * P' - P' * S.PL) * (1 - P') := by noncomm_ring
  have h2 : (1 - P') * comm S.PL P' = comm S.PL P' * P' := by
    dsimp [comm]
    calc (1 - P') * (S.PL * P' - P' * S.PL)
      _ = S.PL * P' - P' * S.PL - P' * S.PL * P' + (P' * P') * S.PL := by noncomm_ring
      _ = S.PL * P' - P' * S.PL * P' := by rw [hP']; abel
      _ = S.PL * (P' * P') - P' * S.PL * P' := by rw [hP']
      _ = (S.PL * P' - P' * S.PL) * P' := by noncomm_ring
  dsimp [comm]
  apply sub_eq_zero.mpr
  calc P' * (comm S.PL P' * comm S.PL P')
    _ = (P' * comm S.PL P') * comm S.PL P' := by rw [mul_assoc]
    _ = (comm S.PL P' * (1 - P')) * comm S.PL P' := by rw [h1]
    _ = comm S.PL P' * ((1 - P') * comm S.PL P') := by rw [mul_assoc]
    _ = comm S.PL P' * (comm S.PL P' * P') := by rw [h2]
    _ = (comm S.PL P' * comm S.PL P') * P' := by rw [← mul_assoc]

/-- **Emergent Grade-2 Bivector from Anticommuting Involution Obstruction**:
Given `R` anticommuting with the chiral grading `G` (`G * R + R * G = 0`), their commutator
equals `2 * (G * R)`, while the grade-2 product `B = G * R` satisfies `B² = -(R²)` and
anticommutes with both `G` and `R`. -/
theorem bivector_from_noncomm_obstruction (R : A)
    (hAnti : G (A := A) * R + R * G (A := A) = 0) :
    comm (G (A := A)) R = (2 : A) * (G (A := A) * R) ∧
    (G (A := A) * R) * (G (A := A) * R) = -(R * R) ∧
    G (A := A) * (G (A := A) * R) + (G (A := A) * R) * G (A := A) = 0 ∧
    (G (A := A) * R) * R + R * (G (A := A) * R) = 0 := by
  have hRG : R * G (A := A) = -(G (A := A) * R) := eq_neg_of_add_eq_zero_right hAnti
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [comm]
    calc G (A := A) * R - R * G (A := A)
      _ = G (A := A) * R - (-(G (A := A) * R)) := by rw [hRG]
      _ = G (A := A) * R + G (A := A) * R := sub_neg_eq_add _ _
      _ = (2 : A) * (G (A := A) * R) := (two_mul _).symm
  · calc (G (A := A) * R) * (G (A := A) * R)
      _ = G (A := A) * (R * G (A := A)) * R := by simp only [mul_assoc]
      _ = G (A := A) * (-(G (A := A) * R)) * R := by rw [hRG]
      _ = -((G (A := A) * G (A := A)) * (R * R)) := by noncomm_ring
      _ = -(R * R) := by rw [G_mul_G, one_mul]
  · calc G (A := A) * (G (A := A) * R) + (G (A := A) * R) * G (A := A)
      _ = (G (A := A) * G (A := A)) * R + G (A := A) * (R * G (A := A)) := by simp only [mul_assoc]
      _ = R + G (A := A) * (-(G (A := A) * R)) := by rw [G_mul_G, one_mul, hRG]
      _ = R - (G (A := A) * G (A := A)) * R := by noncomm_ring
      _ = R - R := by rw [G_mul_G, one_mul]
      _ = 0 := sub_self R
  · calc (G (A := A) * R) * R + R * (G (A := A) * R)
      _ = G (A := A) * (R * R) + (R * G (A := A)) * R := by simp only [mul_assoc]
      _ = G (A := A) * (R * R) + (-(G (A := A) * R)) * R := by rw [hRG]
      _ = G (A := A) * (R * R) - G (A := A) * (R * R) := by noncomm_ring
      _ = 0 := sub_self _

/-- Conjugation by the emergent grade-2 bivector `B = G * R` (with two-sided inverse
`B⁻¹ = R⁻¹ * G` for any invertible sheet-swap `R`) preserves both the even `body` and odd
`soul` subalgebras while swapping the chiral sheets `P_L ↔ P_R`. -/
theorem bivector_preserves_body_and_soul (R Rinv : A)
    (hRL : R * Rinv = 1) (hLR : Rinv * R = 1)
    (hSwapL : R * S.PL * Rinv = S.PR) (X : A) :
    body ((G (A := A) * R) * body X * (Rinv * G (A := A))) =
      (G (A := A) * R) * body X * (Rinv * G (A := A)) ∧
    soul ((G (A := A) * R) * soul X * (Rinv * G (A := A))) =
      (G (A := A) * R) * soul X * (Rinv * G (A := A)) := by
  have hSwapR : R * S.PR * Rinv = S.PL := by
    have h_PR : S.PR = 1 - S.PL := by
      calc S.PR = (S.PL + S.PR) - S.PL := by abel
        _ = 1 - S.PL := by rw [S.h_sum]
    calc R * S.PR * Rinv
      _ = R * (1 - S.PL) * Rinv := by rw [h_PR]
      _ = R * Rinv - R * S.PL * Rinv := by noncomm_ring
      _ = 1 - S.PR := by rw [hRL, hSwapL]
      _ = S.PL := by
          calc 1 - S.PR = (S.PL + S.PR) - S.PR := by rw [S.h_sum]
            _ = S.PL := by abel
  have hBPL : (G (A := A) * R) * S.PL * (Rinv * G (A := A)) = S.PR := by
    calc (G (A := A) * R) * S.PL * (Rinv * G (A := A))
      _ = G (A := A) * (R * S.PL * Rinv) * G (A := A) := by simp only [mul_assoc]
      _ = G (A := A) * S.PR * G (A := A) := by rw [hSwapL]
      _ = (-S.PR) * G (A := A) := by rw [G_mul_PR]
      _ = -(S.PR * G (A := A)) := by rw [neg_mul]
      _ = -(-S.PR) := by rw [PR_mul_G]
      _ = S.PR := neg_neg _
  have hBPR : (G (A := A) * R) * S.PR * (Rinv * G (A := A)) = S.PL := by
    calc (G (A := A) * R) * S.PR * (Rinv * G (A := A))
      _ = G (A := A) * (R * S.PR * Rinv) * G (A := A) := by simp only [mul_assoc]
      _ = G (A := A) * S.PL * G (A := A) := by rw [hSwapR]
      _ = S.PL * G (A := A) := by rw [G_mul_PL]
      _ = S.PL := PL_mul_G
  have hBBinv : (G (A := A) * R) * (Rinv * G (A := A)) = 1 := by
    calc (G (A := A) * R) * (Rinv * G (A := A))
      _ = G (A := A) * (R * Rinv) * G (A := A) := by simp only [mul_assoc]
      _ = G (A := A) * G (A := A) := by rw [hRL, mul_one]
      _ = 1 := G_mul_G
  have hBinvB : (Rinv * G (A := A)) * (G (A := A) * R) = 1 := by
    calc (Rinv * G (A := A)) * (G (A := A) * R)
      _ = Rinv * (G (A := A) * G (A := A)) * R := by simp only [mul_assoc]
      _ = Rinv * R := by rw [G_mul_G, mul_one]
      _ = 1 := hLR
  have hBodyConj : (G (A := A) * R) * body X * (Rinv * G (A := A)) =
      body ((G (A := A) * R) * X * (Rinv * G (A := A))) := by
    dsimp [body]
    calc (G (A := A) * R) * (S.PL * X * S.PL + S.PR * X * S.PR) * (Rinv * G (A := A))
      _ = ((G (A := A) * R) * S.PL * (Rinv * G (A := A))) *
            ((G (A := A) * R) * X * (Rinv * G (A := A))) *
            ((G (A := A) * R) * S.PL * (Rinv * G (A := A))) +
          ((G (A := A) * R) * S.PR * (Rinv * G (A := A))) *
            ((G (A := A) * R) * X * (Rinv * G (A := A))) *
            ((G (A := A) * R) * S.PR * (Rinv * G (A := A))) := by
            simp only [mul_add, add_mul]
            have t1 : (G (A := A) * R) * S.PL * (Rinv * G (A := A)) *
                ((G (A := A) * R) * X * (Rinv * G (A := A))) *
                ((G (A := A) * R) * S.PL * (Rinv * G (A := A))) =
                (G (A := A) * R) * (S.PL * X * S.PL) * (Rinv * G (A := A)) := by
              calc _
                _ = (G (A := A) * R) * S.PL * ((Rinv * G (A := A)) * (G (A := A) * R)) *
                      X * ((Rinv * G (A := A)) * (G (A := A) * R)) * S.PL * (Rinv * G (A := A)) := by
                    simp only [mul_assoc]
                _ = (G (A := A) * R) * (S.PL * X * S.PL) * (Rinv * G (A := A)) := by
                    rw [hBinvB]; simp [mul_assoc]
            have t2 : (G (A := A) * R) * S.PR * (Rinv * G (A := A)) *
                ((G (A := A) * R) * X * (Rinv * G (A := A))) *
                ((G (A := A) * R) * S.PR * (Rinv * G (A := A))) =
                (G (A := A) * R) * (S.PR * X * S.PR) * (Rinv * G (A := A)) := by
              calc _
                _ = (G (A := A) * R) * S.PR * ((Rinv * G (A := A)) * (G (A := A) * R)) *
                      X * ((Rinv * G (A := A)) * (G (A := A) * R)) * S.PR * (Rinv * G (A := A)) := by
                    simp only [mul_assoc]
                _ = (G (A := A) * R) * (S.PR * X * S.PR) * (Rinv * G (A := A)) := by
                    rw [hBinvB]; simp [mul_assoc]
            rw [t1, t2]
      _ = S.PR * ((G (A := A) * R) * X * (Rinv * G (A := A))) * S.PR +
          S.PL * ((G (A := A) * R) * X * (Rinv * G (A := A))) * S.PL := by
            rw [hBPL, hBPR]
      _ = _ := add_comm _ _
  have hSoulConj : (G (A := A) * R) * soul X * (Rinv * G (A := A)) =
      soul ((G (A := A) * R) * X * (Rinv * G (A := A))) := by
    dsimp [soul, soul_LR, soul_RL]
    have t1 : (G (A := A) * R) * S.PL * (Rinv * G (A := A)) *
        ((G (A := A) * R) * X * (Rinv * G (A := A))) *
        ((G (A := A) * R) * S.PR * (Rinv * G (A := A))) =
        (G (A := A) * R) * (S.PL * X * S.PR) * (Rinv * G (A := A)) := by
      calc _
        _ = (G (A := A) * R) * S.PL * ((Rinv * G (A := A)) * (G (A := A) * R)) *
              X * ((Rinv * G (A := A)) * (G (A := A) * R)) * S.PR * (Rinv * G (A := A)) := by
            simp only [mul_assoc]
        _ = (G (A := A) * R) * (S.PL * X * S.PR) * (Rinv * G (A := A)) := by
            rw [hBinvB]; simp [mul_assoc]
    have t2 : (G (A := A) * R) * S.PR * (Rinv * G (A := A)) *
        ((G (A := A) * R) * X * (Rinv * G (A := A))) *
        ((G (A := A) * R) * S.PL * (Rinv * G (A := A))) =
        (G (A := A) * R) * (S.PR * X * S.PL) * (Rinv * G (A := A)) := by
      calc _
        _ = (G (A := A) * R) * S.PR * ((Rinv * G (A := A)) * (G (A := A) * R)) *
              X * ((Rinv * G (A := A)) * (G (A := A) * R)) * S.PL * (Rinv * G (A := A)) := by
            simp only [mul_assoc]
        _ = (G (A := A) * R) * (S.PR * X * S.PL) * (Rinv * G (A := A)) := by
            rw [hBinvB]; simp [mul_assoc]
    calc (G (A := A) * R) * (S.PL * X * S.PR + S.PR * X * S.PL) * (Rinv * G (A := A))
      _ = (G (A := A) * R) * (S.PL * X * S.PR) * (Rinv * G (A := A)) +
          (G (A := A) * R) * (S.PR * X * S.PL) * (Rinv * G (A := A)) := by
            simp only [mul_add, add_mul]
      _ = S.PR * ((G (A := A) * R) * X * (Rinv * G (A := A))) * S.PL +
          S.PL * ((G (A := A) * R) * X * (Rinv * G (A := A))) * S.PR := by
            rw [← t1, ← t2, hBPL, hBPR]
      _ = _ := add_comm _ _
  refine ⟨?_, ?_⟩
  · rw [hBodyConj, body_is_idempotent]
  · rw [hSoulConj, soul_is_idempotent]

end NoncommutativityHigherGrades

end InfoGeometry.Algebra.DeWittPeirceSuperalgebra
