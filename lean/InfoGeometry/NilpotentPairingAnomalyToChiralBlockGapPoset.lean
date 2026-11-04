/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic

namespace OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset

variable {B : Type*} [Ring B] [StarRing B]

/-!
### 0. Minimal Additive Cancellation Helpers
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
private theorem neg_sub_eq_neg_add (a b : B) : -a - b = -(a + b) := by
  rw [sub_eq_add_neg, ← neg_add_rev, add_comm b a]

/-!
### 1. Stage I (`NPA₁–NPA₂`): Non-Commuting Nilpotent Pairing & Parity Anomaly `Σ`
-/

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- **Foundational Object (`NPA₁`):**
    The non-commuting nilpotent pairing / parity anomaly `Σ = [N_+, N_-]`. -/
def Sigma (N_plus : B) : B := comm N_plus (star N_plus)

/-- The commutator anomaly is self-adjoint under the ring involution. -/
theorem Sigma_star (N_plus : B) : star (Sigma N_plus) = Sigma N_plus := by
  dsimp [Sigma, comm]
  rw [star_sub]
  congr 1
  all_goals rw [star_mul, star_star]

/-- Dual nilpotency `(N_-)^2 = 0`. -/
theorem star_N_plus_sq (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    star N_plus * star N_plus = 0 := by
  rw [← star_mul, h_nil, star_zero]

/-- Dual Von Neumann regularity `N_- N_+ N_- = N_-`. -/
theorem star_N_plus_reg (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * N_plus * star N_plus = star N_plus := by
  have h := congrArg star h_reg
  rw [star_mul, star_mul, star_star, ← mul_assoc] at h
  exact h

/-- `NPA₁` Left chiral parity `+1` of `N_+` under `Σ`: `Σ * N_+ = N_+`. -/
theorem Sigma_mul_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * N_plus = N_plus := by
  dsimp [Sigma, comm]
  rw [sub_mul, h_reg, mul_assoc (star N_plus) N_plus N_plus, h_nil, mul_zero, sub_zero]

/-- `NPA₁` Right chiral parity `-1` of `N_+` under `Σ`: `N_+ * Σ = -N_+`. -/
theorem N_plus_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    N_plus * Sigma N_plus = -N_plus := by
  dsimp [Sigma, comm]
  rw [mul_sub, ← mul_assoc N_plus N_plus (star N_plus), h_nil, zero_mul,
      ← mul_assoc N_plus (star N_plus) N_plus, h_reg, zero_sub]

/-- `NPA₁` Left chiral parity `-1` of `N_-` under `Σ`: `Σ * N_- = -N_-`. -/
theorem Sigma_mul_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * star N_plus = -star N_plus := by
  dsimp [Sigma, comm]
  rw [sub_mul, mul_assoc N_plus (star N_plus) (star N_plus),
      star_N_plus_sq N_plus h_nil, mul_zero,
      star_N_plus_reg N_plus h_reg, zero_sub]

/-- `NPA₁` Right chiral parity `+1` of `N_-` under `Σ`: `N_- * Σ = N_-`. -/
theorem star_N_plus_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * Sigma N_plus = star N_plus := by
  dsimp [Sigma, comm]
  rw [mul_sub, ← mul_assoc (star N_plus) N_plus (star N_plus),
      star_N_plus_reg N_plus h_reg,
      ← mul_assoc (star N_plus) (star N_plus) N_plus,
      star_N_plus_sq N_plus h_nil, zero_mul, sub_zero]

/-- **`NPA₂` Chiral Parity Anticommutation Anomaly (`{Σ, N_+} = 0` and `{Σ, N_-} = 0`):** -/
theorem anticomm_Sigma_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Sigma N_plus) N_plus = 0 := by
  dsimp [anticomm]
  rw [Sigma_mul_N_plus N_plus h_nil h_reg,
      N_plus_mul_Sigma N_plus h_nil h_reg,
      ← sub_eq_add_neg, sub_self]

theorem anticomm_Sigma_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Sigma N_plus) (star N_plus) = 0 := by
  dsimp [anticomm]
  rw [Sigma_mul_star_N_plus N_plus h_nil h_reg,
      star_N_plus_mul_Sigma N_plus h_nil h_reg,
      add_comm (-star N_plus) (star N_plus),
      ← sub_eq_add_neg, sub_self]

/-- The commutator action on `N_+` is twice its positive chiral grade. -/
theorem comm_Sigma_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (Sigma N_plus) N_plus = N_plus + N_plus := by
  dsimp [comm]
  rw [Sigma_mul_N_plus N_plus h_nil h_reg,
      N_plus_mul_Sigma N_plus h_nil h_reg,
      sub_eq_add_neg, neg_neg]

/-- The commutator action on `N_-` is twice its negative chiral grade. -/
theorem comm_Sigma_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (Sigma N_plus) (star N_plus) = -(star N_plus + star N_plus) := by
  dsimp [comm]
  rw [Sigma_mul_star_N_plus N_plus h_nil h_reg,
      star_N_plus_mul_Sigma N_plus h_nil h_reg,
      sub_eq_add_neg, ← neg_add]

/-!
### 2. Stage II (`NPA₃–NPA₄`): Chiral Block Operators `Φ`, `J` & Parity Anomaly Action
-/

/-- Self-adjoint chiral block pairing operator `Φ = N_+ + N_-`. -/
def Phi (N_plus : B) : B := N_plus + star N_plus

/-- Skew-adjoint chiral block rotor `J = N_+ - N_-`. -/
def J (N_plus : B) : B := N_plus - star N_plus

/-- `NPA₃` The parity anomaly `Σ` rotates `Φ` into `J`: `Σ * Φ = J`. -/
theorem Sigma_mul_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * Phi N_plus = J N_plus := by
  dsimp [Phi, J]
  rw [mul_add,
      Sigma_mul_N_plus N_plus h_nil h_reg,
      Sigma_mul_star_N_plus N_plus h_nil h_reg,
      ← sub_eq_add_neg]

/-- `NPA₃` Right-multiplying `Φ` by `Σ` produces `-J`: `Φ * Σ = -J`. -/
theorem Phi_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * Sigma N_plus = -J N_plus := by
  dsimp [Phi, J]
  rw [add_mul,
      N_plus_mul_Sigma N_plus h_nil h_reg,
      star_N_plus_mul_Sigma N_plus h_nil h_reg,
      add_comm (-N_plus) (star N_plus),
      ← sub_eq_add_neg, neg_sub]

/-- `NPA₃` The parity anomaly `Σ` rotates `J` back into `Φ`: `Σ * J = Φ`. -/
theorem Sigma_mul_J (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * J N_plus = Phi N_plus := by
  dsimp [Phi, J]
  rw [mul_sub,
      Sigma_mul_N_plus N_plus h_nil h_reg,
      Sigma_mul_star_N_plus N_plus h_nil h_reg,
      sub_eq_add_neg, neg_neg]

/-- `NPA₃` Right-multiplying `J` by `Σ` produces `-Φ`: `J * Σ = -Φ`. -/
theorem J_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    J N_plus * Sigma N_plus = -Phi N_plus := by
  dsimp [Phi, J]
  rw [sub_mul,
      N_plus_mul_Sigma N_plus h_nil h_reg,
      star_N_plus_mul_Sigma N_plus h_nil h_reg,
      neg_sub_eq_neg_add]

/-- `NPA₄` The product of the chiral block operators `J` and `Φ` is the anomaly `Σ`:
    `J * Φ = Σ`. -/
theorem J_mul_Phi (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    J N_plus * Phi N_plus = Sigma N_plus := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  dsimp [J, Phi, Sigma, comm]
  calc (N_plus - star N_plus) * (N_plus + star N_plus)
    _ = (N_plus - star N_plus) * N_plus + (N_plus - star N_plus) * star N_plus := by
        rw [mul_add]
    _ = (N_plus * N_plus - star N_plus * N_plus) +
        (N_plus * star N_plus - star N_plus * star N_plus) := by
        rw [sub_mul, sub_mul]
    _ = (0 - star N_plus * N_plus) + (N_plus * star N_plus - 0) := by
        rw [h_nil, h_star_nil]
    _ = -(star N_plus * N_plus) + N_plus * star N_plus := by rw [zero_sub, sub_zero]
    _ = N_plus * star N_plus + -(star N_plus * N_plus) := by rw [add_comm]
    _ = N_plus * star N_plus - star N_plus * N_plus := by rw [← sub_eq_add_neg]

/-- **`NPA₄` Block Parity Anomaly (`{Σ, Φ} = 0` and `[Σ, Φ] = 2J`):** -/
theorem anticomm_Sigma_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Sigma N_plus) (Phi N_plus) = 0 := by
  dsimp [anticomm]
  rw [Sigma_mul_Phi N_plus h_nil h_reg,
      Phi_mul_Sigma N_plus h_nil h_reg,
      ← sub_eq_add_neg, sub_self]

theorem comm_Sigma_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (Sigma N_plus) (Phi N_plus) = J N_plus + J N_plus := by
  dsimp [comm]
  rw [Sigma_mul_Phi N_plus h_nil h_reg,
      Phi_mul_Sigma N_plus h_nil h_reg,
      sub_eq_add_neg, neg_neg]

/-!
### 3. Stage III (`NPA₅–NPA₈`): Support & Spectral Gap as Downstream Output of `Σ` and `Φ`
-/

/-- **Downstream Support / Spectral Gap (`NPA₅`):**
    Defined directly as the square of the parity anomaly `Gap := Σ * Σ`. -/
def Gap (N_plus : B) : B := Sigma N_plus * Sigma N_plus

/-- The anomaly-square support is self-adjoint. -/
theorem Gap_star (N_plus : B) : star (Gap N_plus) = Gap N_plus := by
  dsimp [Gap]
  rw [star_mul, Sigma_star]

/-- `NPA₅` `Gap` acts as the identity on `N_+`: `Gap * N_+ = N_+`. -/
theorem Gap_mul_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus * N_plus = N_plus := by
  dsimp [Gap]
  rw [mul_assoc,
      Sigma_mul_N_plus N_plus h_nil h_reg,
      Sigma_mul_N_plus N_plus h_nil h_reg]

/-- `NPA₅` `Gap` acts as the identity on `N_-`: `Gap * N_- = N_-`. -/
theorem Gap_mul_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus * star N_plus = star N_plus := by
  dsimp [Gap]
  rw [mul_assoc,
      Sigma_mul_star_N_plus N_plus h_nil h_reg,
      mul_neg,
      Sigma_mul_star_N_plus N_plus h_nil h_reg,
      neg_neg]

/-- `NPA₅` `Gap` absorbs the anomaly `Σ`: `Gap * Σ = Σ`. -/
theorem Gap_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus * Sigma N_plus = Sigma N_plus := by
  dsimp [Sigma, comm]
  rw [mul_sub,
      ← mul_assoc (Gap N_plus) N_plus (star N_plus),
      Gap_mul_N_plus N_plus h_nil h_reg,
      ← mul_assoc (Gap N_plus) (star N_plus) N_plus,
      Gap_mul_star_N_plus N_plus h_nil h_reg]

/-- **`NPA₆` Idempotency of the Anomaly Support (`Gap * Gap = Gap`):** -/
theorem Gap_idem (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus * Gap N_plus = Gap N_plus := by
  calc Gap N_plus * Gap N_plus
    _ = Gap N_plus * (Sigma N_plus * Sigma N_plus) := rfl
    _ = (Gap N_plus * Sigma N_plus) * Sigma N_plus := by rw [← mul_assoc]
    _ = Sigma N_plus * Sigma N_plus := by rw [Gap_mul_Sigma N_plus h_nil h_reg]
    _ = Gap N_plus := rfl

/-- **`NPA₆` The Chiral Block Operator Turns the Anomaly into a Gap (`Φ² = Gap`):**
    Proved directly through the chiral block chain `Φ² = (Σ J) Φ = Σ (J Φ) = Σ² = Gap`. -/
theorem Phi_sq_eq_Gap (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * Phi N_plus = Gap N_plus := by
  calc Phi N_plus * Phi N_plus
    _ = (Sigma N_plus * J N_plus) * Phi N_plus := by
        rw [Sigma_mul_J N_plus h_nil h_reg]
    _ = Sigma N_plus * (J N_plus * Phi N_plus) := by rw [mul_assoc]
    _ = Sigma N_plus * Sigma N_plus := by rw [J_mul_Phi N_plus h_nil]
    _ = Gap N_plus := rfl

/-- **`NPA₇` Decomposition of `Gap` into the Chiral Block Support `P_+ + P_-` (`{N_+, N_-}`):**
    The symmetric anticommutator `{N_+, N_-}` emerges as a derived consequence of `Gap = Σ²`. -/
theorem Gap_eq_anticomm (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus = anticomm N_plus (star N_plus) := by
  dsimp [Gap, anticomm]
  calc Sigma N_plus * (N_plus * star N_plus - star N_plus * N_plus)
    _ = Sigma N_plus * (N_plus * star N_plus) -
        Sigma N_plus * (star N_plus * N_plus) := by rw [mul_sub]
    _ = (Sigma N_plus * N_plus) * star N_plus -
        (Sigma N_plus * star N_plus) * N_plus := by rw [← mul_assoc, ← mul_assoc]
    _ = N_plus * star N_plus - (-star N_plus) * N_plus := by
        rw [Sigma_mul_N_plus N_plus h_nil h_reg,
            Sigma_mul_star_N_plus N_plus h_nil h_reg]
    _ = N_plus * star N_plus + star N_plus * N_plus := by
        rw [neg_mul, sub_eq_add_neg, neg_neg]

/-- **`NPA₈` The Chiral Block Operator Is Gapped on Its Support (`Gap * Φ = Φ` and `Φ³ = Φ`):** -/
theorem Gap_mul_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus * Phi N_plus = Phi N_plus := by
  calc Gap N_plus * Phi N_plus
    _ = Sigma N_plus * (Sigma N_plus * Phi N_plus) := by dsimp [Gap]; rw [mul_assoc]
    _ = Sigma N_plus * J N_plus := by rw [Sigma_mul_Phi N_plus h_nil h_reg]
    _ = Phi N_plus := Sigma_mul_J N_plus h_nil h_reg

/-- The anomaly support acts as a right identity on the chiral block as well:
`Φ * Gap = Φ`. -/
theorem Phi_mul_Gap (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * Gap N_plus = Phi N_plus := by
  calc Phi N_plus * Gap N_plus
    _ = (Phi N_plus * Sigma N_plus) * Sigma N_plus := by
        dsimp [Gap]
        rw [← mul_assoc]
    _ = (-J N_plus) * Sigma N_plus := by
        rw [Phi_mul_Sigma N_plus h_nil h_reg]
    _ = -(J N_plus * Sigma N_plus) := by rw [neg_mul]
    _ = -(-Phi N_plus) := by rw [J_mul_Sigma N_plus h_nil h_reg]
    _ = Phi N_plus := by rw [neg_neg]

/-- The anomaly support fixes the rotor on the left: `Gap * J = J`. -/
theorem Gap_mul_J (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gap N_plus * J N_plus = J N_plus := by
  calc Gap N_plus * J N_plus
    _ = Sigma N_plus * (Sigma N_plus * J N_plus) := by
        dsimp [Gap]
        rw [mul_assoc]
    _ = Sigma N_plus * Phi N_plus := by
        rw [Sigma_mul_J N_plus h_nil h_reg]
    _ = J N_plus := Sigma_mul_Phi N_plus h_nil h_reg

/-- The anomaly support fixes the rotor on the right: `J * Gap = J`. -/
theorem J_mul_Gap (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    J N_plus * Gap N_plus = J N_plus := by
  calc J N_plus * Gap N_plus
    _ = (J N_plus * Sigma N_plus) * Sigma N_plus := by
        dsimp [Gap]
        rw [← mul_assoc]
    _ = (-Phi N_plus) * Sigma N_plus := by
        rw [J_mul_Sigma N_plus h_nil h_reg]
    _ = -(Phi N_plus * Sigma N_plus) := by rw [neg_mul]
    _ = -(-J N_plus) := by rw [Phi_mul_Sigma N_plus h_nil h_reg]
    _ = J N_plus := by rw [neg_neg]

theorem Phi_cube_eq_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * Phi N_plus * Phi N_plus = Phi N_plus := by
  rw [Phi_sq_eq_Gap N_plus h_nil h_reg, Gap_mul_Phi N_plus h_nil h_reg]

/-- The chiral block is supported on `Gap`: `Φ (Φ² - Gap) = 0`.
    This is an algebraic support identity; no spectrum or analytic gap is asserted. -/
theorem chiral_block_support_polynomial (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * (Phi N_plus * Phi N_plus - Gap N_plus) = 0 := by
  rw [Phi_sq_eq_Gap N_plus h_nil h_reg, sub_self, mul_zero]

end OperatorAlgebra.PeirceSpine.NilpotentPairingAnomalyGapPoset
