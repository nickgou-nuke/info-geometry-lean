/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic

/-!
# Emergent Two-Sheet BdG / Krein / Cartan Bridge Without Ambient `1` (`E₁`–`E₆`)

Background-free operator-algebra module over `[Ring B] [StarRing B]` deriving the entire
two-sheeted BdG / Krein / Cartan geometry from a single regular nilpotent `N_+`
(`N_+ * N_+ = 0`, `N_+ * star N_+ * N_+ = N_+`) with **no ambient unit `1`** and no
pre-existing spacetime:

1. **Intrinsic Krein fundamental symmetry** `Σ = [N_+, N_-] = P - Q` acts on the emergent
   sheets by `Σ P = P`, `Σ Q = -Q`, with `Σ² = V` and `Σ V = V Σ = Σ` — no `2P - 1`
   (which would require the ambient `1`) is ever invoked.
2. **Emergent two-sheet Peirce filtration** (`E₁`–`E₃`): every `X` restricted to
   `V X V` splits into the intra-sheet spin connection `Ω_V(X)` and the inter-sheet
   solder frame `Φ_V(X)`; the chiral wings `E_±(X) = P X Q`, `Q X P` are universally
   nilpotent, and the seed `Φ = N_+ + N_-` recovers `N_±` by Von Neumann regularity.
3. **Mode-specific BdG metric and universal null squeezing** (`E₄`–`E₅`):
   `Φ_V(X)² = G_V(X)`, `J_V(X)² = -G_V(X)`, `J_V(X) Φ_V(X) = Σ_V(X) = Σ · G_V(X)`, and
   `(G_V(X) + Σ_V(X)) (G_V(X) - Σ_V(X)) = 0` for **every** fluctuation `X`.
4. **Emergent Élie Cartan curvature–torsion split** (`E₆`): the commutator of two Cartan
   connections `𝓓_V(W, X) = Ω_V(W) + Φ_V(X)` splits exactly into the `Σ`-even Riemann–Cartan
   curvature `𝓡_V` and the `Σ`-odd Élie Cartan torsion `𝓣_V`.

All statements are pure ring identities in `[Ring B] [StarRing B]`; "metric", "curvature",
"torsion", and "vacuum" are naming conventions for the idempotent-support, commutator, and
grading operators precipitated by `N_+`. Cross-references (prose only): the chiral ideal
owners `InfoGeometry.OperatorAlgebra.PeirceSpine.RealBdGKreinChiralIdealTwoSheetBridge`
(`BDG₁`–`BDG₁₀`) and
`InfoGeometry.OperatorAlgebra.PeirceSpine.HiggsFrameDraggingCyclotomicSupercolorPoset`
(`HFD₁`–`HFD₁₀`), whose `S_P = 2P - 1` grading this module replaces by the intrinsic `Σ`.
-/

namespace OperatorAlgebra.PeirceSpine.EmergentTwoSheetBridge

variable {B : Type*} [Ring B] [StarRing B]

/-!
### 0. Additive Cancellation Helpers (Pure `calc` / `rw`, No `ring` or `abel`)
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
private theorem add_sub_add_mid (a m b : B) : (a + m) - (m + b) = a - b := by
  calc (a + m) - (m + b)
    _ = (a + m) - (b + m) := by rw [add_comm m b]
    _ = ((a - b) + b + m) - (b + m) := by rw [sub_add_self a b]
    _ = ((a - b) + (b + m)) - (b + m) := by rw [add_assoc (a - b) b m]
    _ = a - b := by rw [add_sub_self_right]

omit [StarRing B] in
private theorem neg_sub_eq_neg_add (a b : B) : -b - a = -(a + b) := by
  have h : (a + b) + (-b - a) = 0 := by
    calc (a + b) + (-b - a)
      _ = (a + b) + (-b + -a) := by rw [sub_eq_add_neg]
      _ = a + (b + (-b + -a)) := by rw [add_assoc]
      _ = a + ((b + -b) + -a) := by rw [← add_assoc b (-b) (-a)]
      _ = a + ((b - b) + -a) := by rw [← sub_eq_add_neg b b]
      _ = a + (0 + -a) := by rw [sub_self]
      _ = a + -a := by rw [zero_add]
      _ = a - a := by rw [← sub_eq_add_neg]
      _ = 0 := by rw [sub_self]
  calc -b - a
    _ = 0 + (-b - a) := by rw [zero_add]
    _ = (-(a + b) + (a + b)) + (-b - a) := by
        rw [add_comm (-(a + b)) (a + b), ← sub_eq_add_neg (a + b) (a + b), sub_self]
    _ = -(a + b) + ((a + b) + (-b - a)) := by rw [add_assoc]
    _ = -(a + b) + 0 := by rw [h]
    _ = -(a + b) := by rw [add_zero]

omit [StarRing B] in
private theorem add_Four_swap (a b c d : B) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc (a + b) + (c + d)
    _ = a + (b + (c + d)) := by rw [add_assoc]
    _ = a + ((b + c) + d) := by rw [← add_assoc b c d]
    _ = a + ((c + b) + d) := by rw [add_comm b c]
    _ = a + (c + (b + d)) := by rw [add_assoc c b d]
    _ = (a + c) + (b + d) := by rw [← add_assoc]

omit [StarRing B] in
private theorem sub_Four_swap (a b c d : B) :
    (a + b) - (c + d) = (a - c) + (b - d) := by
  calc (a + b) - (c + d)
    _ = (a + b) + -(c + d) := by rw [sub_eq_add_neg]
    _ = (a + b) + (-d - c) := by rw [← neg_sub_eq_neg_add c d]
    _ = (a + b) + (-d + -c) := by rw [sub_eq_add_neg (-d) c]
    _ = (a + b) + (-c + -d) := by rw [add_comm (-d) (-c)]
    _ = (a + -c) + (b + -d) := by rw [add_Four_swap]
    _ = (a - c) + (b - d) := by rw [← sub_eq_add_neg, ← sub_eq_add_neg]

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

omit [StarRing B] in
/-- Noncommutative subtraction reversal: `x - y = -(y - x)`, proved without any
    ambient `1` or commutativity assumption. -/
private theorem sub_eq_neg_sub (x y : B) : x - y = -(y - x) := by
  have h : (x - y) + (y - x) = 0 := by
    calc (x - y) + (y - x)
      _ = (x + -y) + (y + -x) := by rw [sub_eq_add_neg, sub_eq_add_neg]
      _ = (x + y) + (-y + -x) := by rw [add_Four_swap]
      _ = (x + y) + (-x + -y) := by rw [add_comm (-y) (-x)]
      _ = (x + -x) + (y + -y) := by rw [add_Four_swap]
      _ = 0 + 0 := by simp
      _ = 0 := by rw [add_zero]
  calc x - y
    _ = ((x - y) + (y - x)) - (y - x) := by rw [add_sub_self_right]
    _ = 0 - (y - x) := by rw [h]
    _ = -(y - x) := by rw [zero_sub]

/-!
### 1. Emergent Two-Sheet Carrier `(P, Q, V, Σ)` from a Single Nilpotent `N_+` (Zero Ambient `1`)
-/

def anticomm (X Y : B) : B := X * Y + Y * X
def comm (X Y : B) : B := X * Y - Y * X

/-- Emergent Sheet-1 projector `P = N_+ N_-`. -/
def P (N_plus : B) : B := N_plus * star N_plus

/-- Emergent Sheet-2 projector `Q = N_- N_+`. -/
def Q (N_plus : B) : B := star N_plus * N_plus

/-- Emergent two-sheet identity / translation support `V = {N_+, N_-} = P + Q`. -/
def V (N_plus : B) : B := P N_plus + Q N_plus

/-- Intrinsic BdG / Krein fundamental symmetry & uncertainty 2-form `Σ = [N_+, N_-] = P - Q`. -/
def Sigma (N_plus : B) : B := P N_plus - Q N_plus

/-- Seed Grade-1 vector `Φ = N_+ + N_-`. -/
def Phi (N_plus : B) : B := N_plus + star N_plus

/-- Seed Grade-2 elliptic bivector `J = N_+ - N_-`. -/
def J (N_plus : B) : B := N_plus - star N_plus

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
    _ = N_plus * (star N_plus * (star N_plus * N_plus)) := by rw [mul_assoc]
    _ = N_plus * ((star N_plus * star N_plus) * N_plus) := by
        rw [← mul_assoc (star N_plus) (star N_plus) N_plus]
    _ = N_plus * (0 * N_plus) := by rw [star_N_plus_sq N_plus h_nil]
    _ = 0 := by rw [zero_mul, mul_zero]

theorem Q_mul_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    Q N_plus * P N_plus = 0 := by
  dsimp [P, Q]
  calc (star N_plus * N_plus) * (N_plus * star N_plus)
    _ = star N_plus * (N_plus * (N_plus * star N_plus)) := by rw [mul_assoc]
    _ = star N_plus * ((N_plus * N_plus) * star N_plus) := by
        rw [← mul_assoc N_plus N_plus (star N_plus)]
    _ = star N_plus * (0 * star N_plus) := by rw [h_nil]
    _ = 0 := by rw [zero_mul, mul_zero]

/-- **Intrinsic Krein Action on Sheet 1 (`Σ P = P` and `P Σ = P`, No Ambient `1`):** -/
theorem Sigma_mul_P (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * P N_plus = P N_plus := by
  dsimp [Sigma]
  rw [sub_mul, P_idem N_plus h_reg, Q_mul_P N_plus h_nil, sub_zero]

theorem P_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * Sigma N_plus = P N_plus := by
  dsimp [Sigma]
  rw [mul_sub, P_idem N_plus h_reg, P_mul_Q N_plus h_nil, sub_zero]

/-- **Intrinsic Krein Action on Sheet 2 (`Σ Q = -Q` and `Q Σ = -Q`, No Ambient `1`):** -/
theorem Sigma_mul_Q (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * Q N_plus = -Q N_plus := by
  dsimp [Sigma]
  rw [sub_mul, P_mul_Q N_plus h_nil, Q_idem N_plus h_reg, zero_sub]

theorem Q_mul_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Q N_plus * Sigma N_plus = -Q N_plus := by
  dsimp [Sigma]
  rw [mul_sub, Q_mul_P N_plus h_nil, Q_idem N_plus h_reg, zero_sub]

/-- **Intrinsic Para-Kähler / Krein Involution Law (`Σ² = V` and `Σ V = V Σ = Σ`):** -/
theorem Sigma_sq_eq_V (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * Sigma N_plus = V N_plus := by
  calc Sigma N_plus * (P N_plus - Q N_plus)
    _ = Sigma N_plus * P N_plus - Sigma N_plus * Q N_plus := by rw [mul_sub]
    _ = P N_plus - (-Q N_plus) := by
        rw [Sigma_mul_P N_plus h_nil h_reg, Sigma_mul_Q N_plus h_nil h_reg]
    _ = P N_plus + Q N_plus := by rw [sub_eq_add_neg, neg_neg]

theorem Sigma_mul_V_eq_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * V N_plus = Sigma N_plus := by
  calc Sigma N_plus * V N_plus
      = Sigma N_plus * P N_plus + Sigma N_plus * Q N_plus := by
          rw [V, mul_add]
    _ = P N_plus + -Q N_plus := by
          rw [Sigma_mul_P N_plus h_nil h_reg, Sigma_mul_Q N_plus h_nil h_reg]
    _ = Sigma N_plus := by
          rw [← sub_eq_add_neg]
          change P N_plus - Q N_plus = P N_plus - Q N_plus
          rfl

/-- The emergent support is also a right identity for the intrinsic grading:
`V * Σ = Σ`, without introducing an ambient unit. -/
theorem V_mul_Sigma_eq_Sigma (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    V N_plus * Sigma N_plus = Sigma N_plus := by
  calc V N_plus * Sigma N_plus
      = P N_plus * Sigma N_plus + Q N_plus * Sigma N_plus := by
          rw [V, add_mul]
    _ = P N_plus + -Q N_plus := by
          rw [P_mul_Sigma N_plus h_nil h_reg, Q_mul_Sigma N_plus h_nil h_reg]
    _ = Sigma N_plus := by
          rw [Sigma, ← sub_eq_add_neg]

/-!
### 2. Deriving the Two-Sheet Peirce Filtration, Spin Connection & Solder Frame from `N_+`
-/

/-- Restriction of any operator `X : B` to the emergent two-sheet universe `V X V`. -/
def restrictV (N_plus X : B) : B := V N_plus * X * V N_plus

/-- Emergent intra-sheet spin-connection projection `Ω_V(W) = P W P + Q W Q ∈ g_0`. -/
def spinConnV (N_plus W : B) : B :=
  P N_plus * W * P N_plus + Q N_plus * W * Q N_plus

/-- Emergent outward chiral bridge `E_+(X) = P X Q` (`Sheet 2 → Sheet 1`). -/
def wingPlus (N_plus X : B) : B := P N_plus * X * Q N_plus

/-- Emergent inward chiral bridge `E_-(X) = Q X P` (`Sheet 1 → Sheet 2`). -/
def wingMinus (N_plus X : B) : B := Q N_plus * X * P N_plus

/-- Emergent symmetric inter-sheet frame / solder form `Φ_V(X) = P X Q + Q X P ∈ g_{±1}`. -/
def framePhiV (N_plus X : B) : B := wingPlus N_plus X + wingMinus N_plus X

/-- Emergent skew inter-sheet frame / bivector `J_V(X) = P X Q - Q X P ∈ g_{±1}`. -/
def frameJV (N_plus X : B) : B := wingPlus N_plus X - wingMinus N_plus X

/-- **Theorem E₁ (Emergent Two-Sheet Decomposition of `V X V`):**
    Any operator `X` restricted to the emergent universe `V X V` splits canonically into the
    intra-sheet spin connection `Ω_V(X)` and the inter-sheet solder frame `Φ_V(X)`. -/
theorem restrictV_decomp (N_plus X : B) :
    restrictV N_plus X = spinConnV N_plus X + framePhiV N_plus X := by
  dsimp [restrictV, spinConnV, framePhiV, wingPlus, wingMinus, V]
  calc (P N_plus + Q N_plus) * X * (P N_plus + Q N_plus)
    _ = (P N_plus * X + Q N_plus * X) * (P N_plus + Q N_plus) := by rw [add_mul]
    _ = (P N_plus * X + Q N_plus * X) * P N_plus +
        (P N_plus * X + Q N_plus * X) * Q N_plus := by rw [mul_add]
    _ = (P N_plus * X * P N_plus + Q N_plus * X * P N_plus) +
        (P N_plus * X * Q N_plus + Q N_plus * X * Q N_plus) := by rw [add_mul, add_mul]
    _ = (P N_plus * X * P N_plus + Q N_plus * X * P N_plus) +
        (Q N_plus * X * Q N_plus + P N_plus * X * Q N_plus) := by
        rw [add_comm (P N_plus * X * Q N_plus) (Q N_plus * X * Q N_plus)]
    _ = (P N_plus * X * P N_plus + Q N_plus * X * Q N_plus) +
        (Q N_plus * X * P N_plus + P N_plus * X * Q N_plus) := by rw [add_Four_swap]
    _ = (P N_plus * X * P N_plus + Q N_plus * X * Q N_plus) +
        (P N_plus * X * Q N_plus + Q N_plus * X * P N_plus) := by
        rw [add_comm (Q N_plus * X * P N_plus) (P N_plus * X * Q N_plus)]

/-- **Theorem E₂ (Vacuum Seed Recovery):**
    Evaluating `wingPlus` and `wingMinus` on the seed `Φ = N_+ + N_-` recovers `N_+` and `N_-`. -/
theorem wingPlus_Phi_eq_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    wingPlus N_plus (Phi N_plus) = N_plus := by
  have hPN : P N_plus * N_plus = N_plus := h_reg
  have hPsN : P N_plus * star N_plus = 0 := by
    dsimp [P]
    rw [mul_assoc N_plus (star N_plus) (star N_plus), star_N_plus_sq N_plus h_nil, mul_zero]
  have hNQ : N_plus * Q N_plus = N_plus := by
    dsimp [Q]
    rw [← mul_assoc N_plus (star N_plus) N_plus, h_reg]
  dsimp [wingPlus, Phi]
  rw [mul_add, hPN, hPsN, add_zero, hNQ]

theorem wingMinus_Phi_eq_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    wingMinus N_plus (Phi N_plus) = star N_plus := by
  have hQN : Q N_plus * N_plus = 0 := by
    dsimp [Q]
    rw [mul_assoc (star N_plus) N_plus N_plus, h_nil, mul_zero]
  have hQsN : Q N_plus * star N_plus = star N_plus := star_N_plus_reg N_plus h_reg
  have hsNP : star N_plus * P N_plus = star N_plus := by
    dsimp [P]
    rw [← mul_assoc (star N_plus) N_plus (star N_plus), star_N_plus_reg N_plus h_reg]
  dsimp [wingMinus, Phi]
  rw [mul_add, hQN, hQsN, zero_add, hsNP]

/-- **Theorem E₃ (Universal Nilpotency of Inter-Sheet Chiral Wings for Any `X : B`):** -/
theorem wingPlus_sq_zero (N_plus X : B) (h_nil : N_plus * N_plus = 0) :
    wingPlus N_plus X * wingPlus N_plus X = 0 := by
  dsimp [wingPlus]
  calc (P N_plus * X * Q N_plus) * (P N_plus * X * Q N_plus)
    _ = P N_plus * X * (Q N_plus * (P N_plus * X * Q N_plus)) := by rw [mul_assoc]
    _ = P N_plus * X * (Q N_plus * (P N_plus * (X * Q N_plus))) := by
        rw [mul_assoc (P N_plus) X (Q N_plus)]
    _ = P N_plus * X * ((Q N_plus * P N_plus) * (X * Q N_plus)) := by
        rw [← mul_assoc (Q N_plus) (P N_plus) (X * Q N_plus)]
    _ = P N_plus * X * (0 * (X * Q N_plus)) := by rw [Q_mul_P N_plus h_nil]
    _ = 0 := by rw [zero_mul, mul_zero]

theorem wingMinus_sq_zero (N_plus X : B) (h_nil : N_plus * N_plus = 0) :
    wingMinus N_plus X * wingMinus N_plus X = 0 := by
  dsimp [wingMinus]
  calc (Q N_plus * X * P N_plus) * (Q N_plus * X * P N_plus)
    _ = Q N_plus * X * (P N_plus * (Q N_plus * X * P N_plus)) := by rw [mul_assoc]
    _ = Q N_plus * X * (P N_plus * (Q N_plus * (X * P N_plus))) := by
        rw [mul_assoc (Q N_plus) X (P N_plus)]
    _ = Q N_plus * X * ((P N_plus * Q N_plus) * (X * P N_plus)) := by
        rw [← mul_assoc (P N_plus) (Q N_plus) (X * P N_plus)]
    _ = Q N_plus * X * (0 * (X * P N_plus)) := by rw [P_mul_Q N_plus h_nil]
    _ = 0 := by rw [zero_mul, mul_zero]

/-- **Theorem E₄ (Intrinsic Krein Grading of Spin Connection vs. Solder Frame):**
    Without using `1`, the intrinsic Krein symmetry `Σ = P - Q` commutes with `Ω_V(W)`
    and anticommutes with `Φ_V(X)` and `J_V(X)`, with `Σ * Φ_V(X) = J_V(X)`. -/
theorem Sigma_mul_wingPlus (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * wingPlus N_plus X = wingPlus N_plus X := by
  dsimp [wingPlus]
  rw [← mul_assoc (Sigma N_plus) (P N_plus * X) (Q N_plus),
      ← mul_assoc (Sigma N_plus) (P N_plus) X,
      Sigma_mul_P N_plus h_nil h_reg]

theorem wingPlus_mul_Sigma (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    wingPlus N_plus X * Sigma N_plus = -wingPlus N_plus X := by
  dsimp [wingPlus]
  rw [mul_assoc (P N_plus * X) (Q N_plus) (Sigma N_plus),
      Q_mul_Sigma N_plus h_nil h_reg, mul_neg]

theorem Sigma_mul_wingMinus (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * wingMinus N_plus X = -wingMinus N_plus X := by
  dsimp [wingMinus]
  rw [← mul_assoc (Sigma N_plus) (Q N_plus * X) (P N_plus),
      ← mul_assoc (Sigma N_plus) (Q N_plus) X,
      Sigma_mul_Q N_plus h_nil h_reg, neg_mul, neg_mul]

theorem wingMinus_mul_Sigma (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    wingMinus N_plus X * Sigma N_plus = wingMinus N_plus X := by
  dsimp [wingMinus]
  rw [mul_assoc (Q N_plus * X) (P N_plus) (Sigma N_plus),
      P_mul_Sigma N_plus h_nil h_reg]

theorem comm_Sigma_spinConnV (N_plus W : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (Sigma N_plus) (spinConnV N_plus W) = 0 := by
  have hL : Sigma N_plus * spinConnV N_plus W =
            P N_plus * W * P N_plus - Q N_plus * W * Q N_plus := by
    dsimp [spinConnV]
    rw [mul_add,
        ← mul_assoc (Sigma N_plus) (P N_plus * W) (P N_plus),
        ← mul_assoc (Sigma N_plus) (P N_plus) W,
        Sigma_mul_P N_plus h_nil h_reg,
        ← mul_assoc (Sigma N_plus) (Q N_plus * W) (Q N_plus),
        ← mul_assoc (Sigma N_plus) (Q N_plus) W,
        Sigma_mul_Q N_plus h_nil h_reg,
        neg_mul, neg_mul, ← sub_eq_add_neg]
  have hR : spinConnV N_plus W * Sigma N_plus =
            P N_plus * W * P N_plus - Q N_plus * W * Q N_plus := by
    dsimp [spinConnV]
    rw [add_mul,
        mul_assoc (P N_plus * W) (P N_plus) (Sigma N_plus),
        P_mul_Sigma N_plus h_nil h_reg,
        mul_assoc (Q N_plus * W) (Q N_plus) (Sigma N_plus),
        Q_mul_Sigma N_plus h_nil h_reg,
        mul_neg, ← sub_eq_add_neg]
  dsimp [comm]
  rw [hL, hR, sub_self]

theorem Sigma_mul_framePhiV (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * framePhiV N_plus X = frameJV N_plus X := by
  dsimp [framePhiV, frameJV]
  rw [mul_add,
      Sigma_mul_wingPlus N_plus X h_nil h_reg,
      Sigma_mul_wingMinus N_plus X h_nil h_reg,
      ← sub_eq_add_neg]

theorem framePhiV_mul_Sigma (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    framePhiV N_plus X * Sigma N_plus = -frameJV N_plus X := by
  dsimp [framePhiV, frameJV]
  rw [add_mul,
      wingPlus_mul_Sigma N_plus X h_nil h_reg,
      wingMinus_mul_Sigma N_plus X h_nil h_reg,
      add_comm (-wingPlus N_plus X) (wingMinus N_plus X),
      ← sub_eq_add_neg, neg_sub]

/-- Left multiplication by the intrinsic grading rotates the skew frame back
to the symmetric frame: `Σ * J_V(X) = Φ_V(X)`. -/
theorem Sigma_mul_frameJV_eq_framePhiV (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * frameJV N_plus X = framePhiV N_plus X := by
  dsimp [frameJV, framePhiV]
  rw [mul_sub,
      Sigma_mul_wingPlus N_plus X h_nil h_reg,
      Sigma_mul_wingMinus N_plus X h_nil h_reg]
  calc wingPlus N_plus X - -wingMinus N_plus X
      = wingPlus N_plus X + wingMinus N_plus X := by
          rw [sub_eq_add_neg, neg_neg]

/-- Right multiplication by the intrinsic grading sends the skew frame to
the negative symmetric frame: `J_V(X) * Σ = -Φ_V(X)`. -/
theorem frameJV_mul_Sigma_eq_neg_framePhiV (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    frameJV N_plus X * Sigma N_plus = -framePhiV N_plus X := by
  dsimp [frameJV, framePhiV]
  rw [sub_mul,
      wingPlus_mul_Sigma N_plus X h_nil h_reg,
      wingMinus_mul_Sigma N_plus X h_nil h_reg,
      sub_eq_add_neg,
      ← neg_add]

/-- The skew inter-sheet frame also has odd intrinsic Krein parity. -/
theorem anticomm_Sigma_frameJV (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Sigma N_plus) (frameJV N_plus X) = 0 := by
  dsimp [anticomm]
  rw [Sigma_mul_frameJV_eq_framePhiV N_plus X h_nil h_reg,
      frameJV_mul_Sigma_eq_neg_framePhiV N_plus X h_nil h_reg]
  exact add_neg_cancel (framePhiV N_plus X)

theorem anticomm_Sigma_framePhiV (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Sigma N_plus) (framePhiV N_plus X) = 0 := by
  dsimp [anticomm]
  rw [Sigma_mul_framePhiV N_plus X h_nil h_reg,
      framePhiV_mul_Sigma N_plus X h_nil h_reg,
      ← sub_eq_add_neg, sub_self]

/-!
### 3. Mode-Specific BdG Metric `G_V(X)`, Curvature Dipole `Σ_V(X)` & Universal Null Squeezing
-/

/-- Mode-specific emergent metric `G_V(X) = {E_+(X), E_-(X)} = P X Q X P + Q X P X Q`. -/
def metricGV (N_plus X : B) : B :=
  wingPlus N_plus X * wingMinus N_plus X + wingMinus N_plus X * wingPlus N_plus X

/-- Mode-specific emergent curvature dipole `Σ_V(X) = [E_+(X), E_-(X)] = P X Q X P - Q X P X Q`. -/
def curvSigmaV (N_plus X : B) : B :=
  wingPlus N_plus X * wingMinus N_plus X - wingMinus N_plus X * wingPlus N_plus X

theorem framePhiV_sq_eq_metricGV (N_plus X : B) (h_nil : N_plus * N_plus = 0) :
    framePhiV N_plus X * framePhiV N_plus X = metricGV N_plus X := by
  dsimp [framePhiV, metricGV]
  rw [mul_add, add_mul, add_mul,
      wingPlus_sq_zero N_plus X h_nil, wingMinus_sq_zero N_plus X h_nil,
      zero_add, add_zero, add_comm (wingMinus N_plus X * wingPlus N_plus X)]

theorem frameJV_sq_eq_neg_metricGV (N_plus X : B) (h_nil : N_plus * N_plus = 0) :
    frameJV N_plus X * frameJV N_plus X = -metricGV N_plus X := by
  dsimp [frameJV, metricGV]
  rw [mul_sub, sub_mul, sub_mul,
      wingPlus_sq_zero N_plus X h_nil, wingMinus_sq_zero N_plus X h_nil,
      zero_sub, sub_zero, neg_sub_eq_neg_add]

theorem frameJV_mul_framePhiV (N_plus X : B) (h_nil : N_plus * N_plus = 0) :
    frameJV N_plus X * framePhiV N_plus X = curvSigmaV N_plus X := by
  dsimp [frameJV, framePhiV, curvSigmaV]
  rw [mul_add, sub_mul, sub_mul,
      wingPlus_sq_zero N_plus X h_nil, wingMinus_sq_zero N_plus X h_nil,
      zero_sub, sub_zero, add_comm (-(wingMinus N_plus X * wingPlus N_plus X)),
      ← sub_eq_add_neg]

theorem Sigma_mul_metricGV_eq_curvSigmaV (N_plus X : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Sigma N_plus * metricGV N_plus X = curvSigmaV N_plus X := by
  dsimp [metricGV, curvSigmaV]
  rw [mul_add,
      ← mul_assoc (Sigma N_plus) (wingPlus N_plus X) (wingMinus N_plus X),
      Sigma_mul_wingPlus N_plus X h_nil h_reg,
      ← mul_assoc (Sigma N_plus) (wingMinus N_plus X) (wingPlus N_plus X),
      Sigma_mul_wingMinus N_plus X h_nil h_reg,
      neg_mul, ← sub_eq_add_neg]

/-- **Theorem E₅ (Universal Hyperbolic Null Lightcone Squeezing for Every Fluctuation `X : B`):**
    For EVERY operator `X : B`, the mode-specific geometric tensor `G_V(X) + Σ_V(X)` and its
    Krein reversion `G_V(X) - Σ_V(X)` satisfy `(G_V(X) + Σ_V(X))(G_V(X) - Σ_V(X)) = 0`! -/
theorem universal_mode_hyperbolic_null_squeezing (N_plus X : B)
    (h_nil : N_plus * N_plus = 0) :
    (metricGV N_plus X + curvSigmaV N_plus X) *
    (metricGV N_plus X - curvSigmaV N_plus X) = 0 := by
  let A := wingPlus N_plus X * wingMinus N_plus X
  let D := wingMinus N_plus X * wingPlus N_plus X
  have hAD : A * D = 0 := by
    dsimp [A, D]
    calc (wingPlus N_plus X * wingMinus N_plus X) * (wingMinus N_plus X * wingPlus N_plus X)
      _ = wingPlus N_plus X *
          (wingMinus N_plus X * (wingMinus N_plus X * wingPlus N_plus X)) := by
          rw [mul_assoc (wingPlus N_plus X) (wingMinus N_plus X)
            (wingMinus N_plus X * wingPlus N_plus X)]
      _ = wingPlus N_plus X *
          ((wingMinus N_plus X * wingMinus N_plus X) * wingPlus N_plus X) := by
          rw [← mul_assoc (wingMinus N_plus X) (wingMinus N_plus X) (wingPlus N_plus X)]
      _ = wingPlus N_plus X * (0 * wingPlus N_plus X) := by
          rw [wingMinus_sq_zero N_plus X h_nil]
      _ = 0 := by rw [zero_mul, mul_zero]
  have hSum : metricGV N_plus X + curvSigmaV N_plus X = A + A := by
    dsimp [metricGV, curvSigmaV, A, D]
    calc (A + D) + (A - D)
      _ = (A - D) + (A + D) := by rw [add_comm (A + D) (A - D)]
      _ = (A - D) + (D + A) := by rw [add_comm A D]
      _ = ((A - D) + D) + A := by rw [← add_assoc (A - D) D A]
      _ = A + A := by rw [sub_add_self]
  have hDiff : metricGV N_plus X - curvSigmaV N_plus X = D + D := by
    dsimp [metricGV, curvSigmaV, A, D]
    exact sub_add_sub_cancel_two (wingPlus N_plus X * wingMinus N_plus X)
      (wingMinus N_plus X * wingPlus N_plus X)
  rw [hSum, hDiff, mul_add, add_mul, hAD, add_zero, add_zero]

/-!
### 4. Emergent Élie Cartan Curvature & Torsion Strictly Inside the Two-Sheet Support `V`
-/

/-- Intrinsic Cartan connection `𝓓_V(W, X) = Ω_V(W) + Φ_V(X)` inside `V B V`. -/
def cartanConnV (N_plus W X : B) : B :=
  spinConnV N_plus W + framePhiV N_plus X

/-- Emergent Riemann–Cartan Curvature `𝓡_V = [Ω_V(W₁), Ω_V(W₂)] + [Φ_V(X₁), Φ_V(X₂)]`. -/
def riemannCurvV (N_plus W₁ X₁ W₂ X₂ : B) : B :=
  comm (spinConnV N_plus W₁) (spinConnV N_plus W₂) +
  comm (framePhiV N_plus X₁) (framePhiV N_plus X₂)

/-- Emergent Élie Cartan Torsion `𝓣_V = [Ω_V(W₁), Φ_V(X₂)] - [Ω_V(W₂), Φ_V(X₁)]`. -/
def cartanTorsionV (N_plus W₁ X₁ W₂ X₂ : B) : B :=
  comm (spinConnV N_plus W₁) (framePhiV N_plus X₂) -
  comm (spinConnV N_plus W₂) (framePhiV N_plus X₁)

/-- **Master Theorem E₆ (Emergent Cartan Curvature–Torsion Split from Pure Nilpotent Data):**
    The commutator `[𝓓_V(W₁, X₁), 𝓓_V(W₂, X₂)]` of two emergent Cartan connections splits
    exactly into `𝓡_V + 𝓣_V` without assuming any background manifold! -/
theorem emergent_cartan_curvature_torsion_split (N_plus W₁ X₁ W₂ X₂ : B) :
    comm (cartanConnV N_plus W₁ X₁) (cartanConnV N_plus W₂ X₂) =
      riemannCurvV N_plus W₁ X₁ W₂ X₂ + cartanTorsionV N_plus W₁ X₁ W₂ X₂ := by
  let Ω₁ := spinConnV N_plus W₁
  let Φ₁ := framePhiV N_plus X₁
  let Ω₂ := spinConnV N_plus W₂
  let Φ₂ := framePhiV N_plus X₂
  dsimp [cartanConnV, riemannCurvV, cartanTorsionV, comm]
  change (Ω₁ + Φ₁) * (Ω₂ + Φ₂) - (Ω₂ + Φ₂) * (Ω₁ + Φ₁) =
         ((Ω₁ * Ω₂ - Ω₂ * Ω₁) + (Φ₁ * Φ₂ - Φ₂ * Φ₁)) +
         ((Ω₁ * Φ₂ - Φ₂ * Ω₁) - (Ω₂ * Φ₁ - Φ₁ * Ω₂))
  have hL : (Ω₁ + Φ₁) * (Ω₂ + Φ₂) = (Ω₁ * Ω₂ + Φ₁ * Φ₂) + (Ω₁ * Φ₂ + Φ₁ * Ω₂) := by
    calc (Ω₁ + Φ₁) * (Ω₂ + Φ₂)
      _ = (Ω₁ + Φ₁) * Ω₂ + (Ω₁ + Φ₁) * Φ₂ := by rw [mul_add]
      _ = (Ω₁ * Ω₂ + Φ₁ * Ω₂) + (Ω₁ * Φ₂ + Φ₁ * Φ₂) := by rw [add_mul, add_mul]
      _ = (Ω₁ * Ω₂ + Φ₁ * Ω₂) + (Φ₁ * Φ₂ + Ω₁ * Φ₂) := by
          rw [add_comm (Ω₁ * Φ₂) (Φ₁ * Φ₂)]
      _ = (Ω₁ * Ω₂ + Φ₁ * Φ₂) + (Φ₁ * Ω₂ + Ω₁ * Φ₂) := by rw [add_Four_swap]
      _ = (Ω₁ * Ω₂ + Φ₁ * Φ₂) + (Ω₁ * Φ₂ + Φ₁ * Ω₂) := by
          rw [add_comm (Φ₁ * Ω₂) (Ω₁ * Φ₂)]
  have hR : (Ω₂ + Φ₂) * (Ω₁ + Φ₁) = (Ω₂ * Ω₁ + Φ₂ * Φ₁) + (Φ₂ * Ω₁ + Ω₂ * Φ₁) := by
    calc (Ω₂ + Φ₂) * (Ω₁ + Φ₁)
      _ = (Ω₂ + Φ₂) * Ω₁ + (Ω₂ + Φ₂) * Φ₁ := by rw [mul_add]
      _ = (Ω₂ * Ω₁ + Φ₂ * Ω₁) + (Ω₂ * Φ₁ + Φ₂ * Φ₁) := by rw [add_mul, add_mul]
      _ = (Ω₂ * Ω₁ + Φ₂ * Ω₁) + (Φ₂ * Φ₁ + Ω₂ * Φ₁) := by
          rw [add_comm (Ω₂ * Φ₁) (Φ₂ * Φ₁)]
      _ = (Ω₂ * Ω₁ + Φ₂ * Φ₁) + (Φ₂ * Ω₁ + Ω₂ * Φ₁) := by rw [add_Four_swap]
  have hTors : (Ω₁ * Φ₂ + Φ₁ * Ω₂) - (Φ₂ * Ω₁ + Ω₂ * Φ₁) =
               (Ω₁ * Φ₂ - Φ₂ * Ω₁) - (Ω₂ * Φ₁ - Φ₁ * Ω₂) := by
    rw [sub_Four_swap (Ω₁ * Φ₂) (Φ₁ * Ω₂) (Φ₂ * Ω₁) (Ω₂ * Φ₁),
        sub_eq_neg_sub (Φ₁ * Ω₂) (Ω₂ * Φ₁),
        ← sub_eq_add_neg]
  rw [hL, hR,
      sub_Four_swap (Ω₁ * Ω₂ + Φ₁ * Φ₂) (Ω₁ * Φ₂ + Φ₁ * Ω₂)
                    (Ω₂ * Ω₁ + Φ₂ * Φ₁) (Φ₂ * Ω₁ + Ω₂ * Φ₁),
      sub_Four_swap (Ω₁ * Ω₂) (Φ₁ * Φ₂) (Ω₂ * Ω₁) (Φ₂ * Φ₁),
      hTors]

end OperatorAlgebra.PeirceSpine.EmergentTwoSheetBridge
