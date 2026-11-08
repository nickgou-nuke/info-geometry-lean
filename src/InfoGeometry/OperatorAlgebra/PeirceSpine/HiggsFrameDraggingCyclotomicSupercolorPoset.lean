/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic

/-!
# Higgs Frame-Dragging, Cyclotomic Minima, and Supercolor Emergence Poset (`HFD₁ ≺ ⋯ ≺ HFD₁₀`)

Background-free operator-algebra chain over `[Ring B] [StarRing B]` realizing the
causal dependence **nilpotent interaction → symmetry breaking → gap → emergent
translation grading**, with no ambient spacetime assumed anywhere:

1. **`HFD₁` Unbroken Mexican-Hat Operator Potential**: the symmetric mode
   `Φ = N_+ + N_-` satisfies `Φ² = V` (condensate bandgap support) and the
   Landau–Ginzburg stationarity `Φ⁴ - Φ² = 0` (`V² = V`).
2. **`HFD₂` Cyclotomic Operator Ring Pairing**: the chiral operator
   `C_cyc(u) = u P + (1 - u) Q` pairs the two roots `u, 1 - u` of
   `Φ₆(u) = u² - u + 1 = 0` (base of `Φ₁₂(ω) = Φ₆(ω²)`, `Φ₂₄(τ) = Φ₆(τ⁴)`) with
   the two Peirce sheets; naming per
   `InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicGaloisNilpotentSylvesterSynthesis`,
   no root of `Φ₆` is constructed here — `u` is an arbitrary ring element.
3. **`HFD₃–HFD₅` Frame-Dragging / Spin Cranking**: `±Σ = ±[N_+, N_-]` splits the
   bandgap into cranked potentials `H_crank⁺ = 2P`, `H_crank⁻ = 2Q` selecting the
   cyclotomic eigenvalues `u` and `1 - u`, with the Galois–spin locking
   `C_cyc(u) - C_cyc(1 - u) = (u - (1 - u)) Σ`.
4. **`HFD₆–HFD₇` Amplitude vs. Rotor**: `{P, Φ} = Φ` (massive amplitude mode) and
   `[P, Φ] = J` (Goldstone rotor, `J² = -V`), with feedback `[J, Φ] = 2Σ`.
5. **`HFD₈–HFD₁₀` Supercolor Emergence**: the nilpotents act as chiral parity
   supercharges (`{Γ_chiral, N_±} = 0`); their super-anticommutator
   `P_poincare := {N_+, N_-} = V` is the emergent translation generator, and
   `[P_poincare(N_a), P_poincare(N_b)] = 0` gives the multi-channel closure.

All statements are pure ring identities; "mass", "bandgap", "vacuum", and
"Poincaré" are naming conventions for the idempotent support, splitting, and
grading operators — no metric, time evolution, or continuum limit is claimed.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.HFDArchetype

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
private theorem add_add_sub_cancel (a b : B) : (a + b) + (a - b) = a + a := by
  calc (a + b) + (a - b)
    _ = (a - b) + (a + b) := by rw [add_comm (a + b) (a - b)]
    _ = (a - b) + (b + a) := by rw [add_comm a b]
    _ = ((a - b) + b) + a := by rw [← add_assoc (a - b) b a]
    _ = a + a := by rw [sub_add_self]

omit [StarRing B] in
private theorem inner_four_cancel (b c e f : B) :
    (e + f) + ((c - e) - (f - b)) = b + c := by
  have hef : e + f = (f - b) + (b + e) := by
    calc e + f
      _ = f + e := by rw [add_comm e f]
      _ = ((f - b) + b) + e := by rw [sub_add_self f b]
      _ = (f - b) + (b + e) := by rw [add_assoc (f - b) b e]
  calc (e + f) + ((c - e) - (f - b))
    _ = ((c - e) - (f - b)) + (e + f) := by rw [add_comm (e + f)]
    _ = ((c - e) - (f - b)) + ((f - b) + (b + e)) := by rw [hef]
    _ = (((c - e) - (f - b)) + (f - b)) + (b + e) := by
        rw [← add_assoc ((c - e) - (f - b)) (f - b) (b + e)]
    _ = (c - e) + (b + e) := by rw [sub_add_self (c - e) (f - b)]
    _ = (c - e) + (e + b) := by rw [add_comm b e]
    _ = ((c - e) + e) + b := by rw [← add_assoc (c - e) e b]
    _ = c + b := by rw [sub_add_self c e]
    _ = b + c := by rw [add_comm c b]

omit [StarRing B] in
/-- Universal noncommutative 2-sheet linear difference identity:
    `(a * p + b * q) - (b * p + a * q) = (a - b) * (p - q)`. -/
private theorem two_sheet_linear_diff (a b p q : B) :
    (a * p + b * q) - (b * p + a * q) = (a - b) * (p - q) := by
  have h1 : (a * p + b * q) - (b * p + a * q) =
            (a * p - b * p) - (a * q - b * q) := by
    have h_sum := inner_four_cancel (b * q) (a * p) (b * p) (a * q)
    rw [add_comm (b * q) (a * p)] at h_sum
    calc (a * p + b * q) - (b * p + a * q)
      _ = ((b * p + a * q) + ((a * p - b * p) - (a * q - b * q))) -
          (b * p + a * q) := by rw [h_sum]
      _ = (a * p - b * p) - (a * q - b * q) := by rw [add_sub_self_left]
  rw [h1, ← sub_mul, ← sub_mul, ← mul_sub]

/-!
### 1. Core Operators: Condensate Bandgap `V`, Spin Cranking `Σ`, Higgs `Φ`, Goldstone `J`
-/

/-- Ring commutator `[X, Y] = X Y - Y X`. -/
def comm (X Y : B) : B := X * Y - Y * X

/-- Ring anticommutator `{X, Y} = X Y + Y X`. -/
def anticomm (X Y : B) : B := X * Y + Y * X

/-- Sheet `+` Higgs vacuum projector `P = N_+ N_-`. -/
def P (N_plus : B) : B := N_plus * star N_plus

/-- Sheet `-` dual vacuum projector `Q = N_- N_+`. -/
def Q (N_plus : B) : B := star N_plus * N_plus

/-- Condensate Spectral Bandgap / Emergent Poincaré Translation `V = {N_+, N_-} = P + Q`. -/
def V (N_plus : B) : B := N_plus * star N_plus + star N_plus * N_plus

/-- Magnetogravity / Frame-Dragging Spin-Cranking Generator `Σ = [N_+, N_-] = P - Q`. -/
def Sigma (N_plus : B) : B := N_plus * star N_plus - star N_plus * N_plus

/-- Massive Higgs Amplitude Mode `Φ = N_+ + N_-`. -/
def Phi (N_plus : B) : B := N_plus + star N_plus

/-- Nambu–Goldstone Phase Rotor `J = N_+ - N_-`. -/
def J (N_plus : B) : B := N_plus - star N_plus

/-- Negative-cranked Frame-Dragging Potential `H_crank⁻ = V - Σ` (selects vacuum `P`). -/
def H_crank_minus (N_plus : B) : B := V N_plus - Sigma N_plus

/-- Positive-cranked Frame-Dragging Potential `H_crank⁺ = V + Σ` (selects vacuum `Q`). -/
def H_crank_plus (N_plus : B) : B := V N_plus + Sigma N_plus

/-- Cyclotomic Chiral Operator `C_cyc(u, N_+) = u P + (1 - u) Q` pairing Galois roots
    `u` and `1 - u` of `Φ₆(u) = u² - u + 1 = 0` with the chiral sheets `P` and `Q`. -/
def C_cyc (u N_plus : B) : B := u * P N_plus + (1 - u) * Q N_plus

/-- Supercolor Chiral Parity Grading Operator `Γ_chiral = 2P - 1`. -/
def Gamma_chiral (N_plus : B) : B := P N_plus + P N_plus - 1

/-- Emergent Poincaré Translation Generator `P_poincare = {Q_+, Q_-} = V`. -/
def P_poincare (N_plus : B) : B := anticomm N_plus (star N_plus)

/-!
### 2. Foundational Nilpotent & Projector Identities (`HFD₁`)
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

theorem P_mul_N_plus (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * N_plus = N_plus := h_reg

theorem N_plus_mul_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    N_plus * P N_plus = 0 := by
  dsimp [P]; rw [← mul_assoc, h_nil, zero_mul]

theorem P_mul_star_N_plus (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    P N_plus * star N_plus = 0 := by
  dsimp [P]; rw [mul_assoc, star_N_plus_sq N_plus h_nil, mul_zero]

theorem star_N_plus_mul_P (N_plus : B) (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    star N_plus * P N_plus = star N_plus := by
  dsimp [P]; rw [← mul_assoc, star_N_plus_reg N_plus h_reg]

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

/-- **`HFD₁` The Higgs Square Equals the Condensate Bandgap (`Φ² = V`):** -/
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

/-- **`HFD₁` Landau–Ginzburg / Mexican-Hat Operator Stationarity (`Φ⁴ - Φ² = 0`):**
    The Higgs amplitude operator `Φ` identically satisfies the quartic Mexican-hat
    stationarity polynomial `(Φ²)² - Φ² = V² - V = 0`. -/
theorem higgs_quartic_stationarity (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    (Phi N_plus * Phi N_plus) * (Phi N_plus * Phi N_plus) -
    (Phi N_plus * Phi N_plus) = 0 := by
  rw [Phi_sq_eq_V N_plus h_nil, V_idem N_plus h_nil h_reg, sub_self]

/-!
### 3. Frame-Dragging / Magnetogravity Spin-Cranking & Cyclotomic Minima (`HFD₂–HFD₅`)
-/

theorem H_crank_plus_eq_two_P (N_plus : B) :
    H_crank_plus N_plus = P N_plus + P N_plus := by
  dsimp [H_crank_plus, V, Sigma, P]
  exact add_add_sub_cancel (N_plus * star N_plus) (star N_plus * N_plus)

theorem H_crank_minus_eq_two_Q (N_plus : B) :
    H_crank_minus N_plus = Q N_plus + Q N_plus := by
  dsimp [H_crank_minus, V, Sigma, Q]
  exact sub_add_sub_cancel_two (N_plus * star N_plus) (star N_plus * N_plus)

/-- **`HFD₃` Frame-Dragging Vacuum Selection I (`H_crank⁻ * P = 0`):**
    The cranked potential `H_crank⁻ = V - Σ` selects Sheet `+` (`P`) as its
    exact zero-energy Higgs vacuum minimum. -/
theorem H_crank_minus_mul_P (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    H_crank_minus N_plus * P N_plus = 0 := by
  rw [H_crank_minus_eq_two_Q, add_mul, Q_mul_P N_plus h_nil, add_zero]

/-- **`HFD₃` Frame-Dragging Bandgap Excitation (`H_crank⁻ * Q = 2Q`):**
    While `P` is a zero-energy minimum of `H_crank⁻`, the opposite sheet `Q`
    is lifted across the condensate bandgap to `2Q`. -/
theorem H_crank_minus_mul_Q (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    H_crank_minus N_plus * Q N_plus = Q N_plus + Q N_plus := by
  rw [H_crank_minus_eq_two_Q, add_mul, Q_idem N_plus h_reg]

/-- **`HFD₃` Opposite Frame-Dragging Vacuum Selection (`H_crank⁺ * Q = 0`):**
    Reversing the frame-dragging cranking sign (`V + Σ`) selects Sheet `-` (`Q`)
    as the zero-energy vacuum minimum. -/
theorem H_crank_plus_mul_Q (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    H_crank_plus N_plus * Q N_plus = 0 := by
  rw [H_crank_plus_eq_two_P, add_mul, P_mul_Q N_plus h_nil, add_zero]

/-- **`HFD₃` Secular Factorization of the Cranked Potentials (`H_crank⁺ * H_crank⁻ = 0`):** -/
theorem H_crank_secular_product (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    H_crank_plus N_plus * H_crank_minus N_plus = 0 := by
  rw [H_crank_plus_eq_two_P, H_crank_minus_eq_two_Q,
      mul_add, add_mul, P_mul_Q N_plus h_nil, add_zero, add_zero]

/-- **`HFD₄` Cyclotomic Minimum Projection on Sheet `+` (`C_cyc(u) * P = u P`):** -/
theorem C_cyc_mul_P (u N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    C_cyc u N_plus * P N_plus = u * P N_plus := by
  dsimp [C_cyc]
  rw [add_mul,
      mul_assoc u (P N_plus) (P N_plus), P_idem N_plus h_reg,
      mul_assoc (1 - u) (Q N_plus) (P N_plus), Q_mul_P N_plus h_nil,
      mul_zero, add_zero]

/-- **`HFD₄` Cyclotomic Minimum Projection on Sheet `-` (`C_cyc(u) * Q = (1 - u) Q`):** -/
theorem C_cyc_mul_Q (u N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    C_cyc u N_plus * Q N_plus = (1 - u) * Q N_plus := by
  dsimp [C_cyc]
  rw [add_mul,
      mul_assoc u (P N_plus) (Q N_plus), P_mul_Q N_plus h_nil,
      mul_assoc (1 - u) (Q N_plus) (Q N_plus), Q_idem N_plus h_reg,
      mul_zero, zero_add]

/-- **`HFD₄` Cranked Condensate Selects Cyclotomic Eigenvalue `u` (`C_cyc(u) H_crank⁺ = u H_crank⁺`):** -/
theorem C_cyc_mul_H_crank_plus (u N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    C_cyc u N_plus * H_crank_plus N_plus = u * H_crank_plus N_plus := by
  rw [H_crank_plus_eq_two_P, mul_add, C_cyc_mul_P u N_plus h_nil h_reg, ← mul_add]

/-- **`HFD₄` Dual Cranked Condensate Selects Galois Conjugate `1 - u` (`C_cyc(u) H_crank⁻ = (1 - u) H_crank⁻`):** -/
theorem C_cyc_mul_H_crank_minus (u N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    C_cyc u N_plus * H_crank_minus N_plus = (1 - u) * H_crank_minus N_plus := by
  rw [H_crank_minus_eq_two_Q, mul_add, C_cyc_mul_Q u N_plus h_nil h_reg, ← mul_add]

/-- **`HFD₅` Galois–Spin Locking Identity (`C_cyc(u) - C_cyc(1 - u) = (u - (1 - u)) Σ`):**
    The asymmetry between the cyclotomic operator `C_cyc(u)` and its Galois-conjugate
    partner `C_cyc(1 - u)` is driven directly by the magnetogravity spin-cranking field `Σ`. -/
theorem C_cyc_galois_spin_locking (u N_plus : B) :
    C_cyc u N_plus - C_cyc (1 - u) N_plus =
      (u - (1 - u)) * Sigma N_plus := by
  have h1_sub : 1 - (1 - u) = u := by
    calc 1 - (1 - u)
      _ = ((1 - u) + u) - (1 - u) := by rw [sub_add_self 1 u]
      _ = u := by rw [add_sub_self_left]
  dsimp [C_cyc]
  rw [h1_sub]
  exact two_sheet_linear_diff u (1 - u) (P N_plus) (Q N_plus)

/-!
### 4. Higgs Amplitude (`Φ`) vs. Nambu–Goldstone Rotor (`J`) Splitting (`HFD₆–HFD₇`)
-/

theorem P_mul_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    P N_plus * Phi N_plus = N_plus := by
  dsimp [Phi]
  rw [mul_add, P_mul_N_plus N_plus h_reg, P_mul_star_N_plus N_plus h_nil, add_zero]

theorem Phi_mul_P (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Phi N_plus * P N_plus = star N_plus := by
  dsimp [Phi]
  rw [add_mul, N_plus_mul_P N_plus h_nil, star_N_plus_mul_P N_plus h_reg, zero_add]

/-- **`HFD₆` Massive Higgs Amplitude Projection (`{P, Φ} = Φ`):**
    The anticommutator of the selected vacuum minimum `P` with `Φ` preserves the
    massive Higgs amplitude mode `Φ = N_+ + N_-`. -/
theorem anticomm_P_Phi_eq_Phi (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (P N_plus) (Phi N_plus) = Phi N_plus := by
  dsimp [anticomm]
  rw [P_mul_Phi N_plus h_nil h_reg, Phi_mul_P N_plus h_nil h_reg]
  rfl

/-- **`HFD₆` Nambu–Goldstone Rotor Generation (`[P, Φ] = J`):**
    The commutator of the broken-symmetry vacuum minimum `P` with `Φ` generates
    the Nambu–Goldstone rotor `J = N_+ - N_-`. -/
theorem comm_P_Phi_eq_J (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (P N_plus) (Phi N_plus) = J N_plus := by
  dsimp [comm]
  rw [P_mul_Phi N_plus h_nil h_reg, Phi_mul_P N_plus h_nil h_reg]
  rfl

/-- **`HFD₇` Goldstone–Higgs Feedback into Spin Curvature (`[J, Φ] = 2Σ`):**
    The commutator of the Goldstone rotor `J` and the Higgs amplitude mode `Φ`
    regenerates twice the magnetogravity spin-cranking field `Σ`. -/
theorem comm_J_Phi_eq_two_Sigma (N_plus : B) (h_nil : N_plus * N_plus = 0) :
    comm (J N_plus) (Phi N_plus) = Sigma N_plus + Sigma N_plus := by
  have h_star_nil := star_N_plus_sq N_plus h_nil
  have hJPhi : J N_plus * Phi N_plus = Sigma N_plus := by
    dsimp [J, Phi, Sigma]
    calc (N_plus - star N_plus) * (N_plus + star N_plus)
      _ = (N_plus - star N_plus) * N_plus + (N_plus - star N_plus) * star N_plus := by
          rw [mul_add]
      _ = (N_plus * N_plus - star N_plus * N_plus) +
          (N_plus * star N_plus - star N_plus * star N_plus) := by rw [sub_mul, sub_mul]
      _ = (0 - star N_plus * N_plus) + (N_plus * star N_plus - 0) := by
          rw [h_nil, h_star_nil]
      _ = -(star N_plus * N_plus) + N_plus * star N_plus := by rw [zero_sub, sub_zero]
      _ = N_plus * star N_plus + -(star N_plus * N_plus) := by rw [add_comm]
      _ = N_plus * star N_plus - star N_plus * N_plus := by rw [← sub_eq_add_neg]
  have hPhiJ : Phi N_plus * J N_plus = -Sigma N_plus := by
    dsimp [J, Phi, Sigma]
    calc (N_plus + star N_plus) * (N_plus - star N_plus)
      _ = (N_plus + star N_plus) * N_plus - (N_plus + star N_plus) * star N_plus := by
          rw [mul_sub]
      _ = (N_plus * N_plus + star N_plus * N_plus) -
          (N_plus * star N_plus + star N_plus * star N_plus) := by rw [add_mul, add_mul]
      _ = (0 + star N_plus * N_plus) - (N_plus * star N_plus + 0) := by
          rw [h_nil, h_star_nil]
      _ = star N_plus * N_plus - N_plus * star N_plus := by rw [zero_add, add_zero]
      _ = -(N_plus * star N_plus - star N_plus * N_plus) := by rw [neg_sub]
  dsimp [comm]
  rw [hJPhi, hPhiJ, sub_eq_add_neg, neg_neg]

/-!
### 5. Supercolor Chiral Parity Supercharges & Emergent Poincaré Spacetime (`HFD₈–HFD₁₀`)
-/

theorem Gamma_chiral_mul_N_plus (N_plus : B)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    Gamma_chiral N_plus * N_plus = N_plus := by
  dsimp [Gamma_chiral]
  rw [sub_mul, add_mul, one_mul, P_mul_N_plus N_plus h_reg, add_sub_self_right]

theorem N_plus_mul_Gamma_chiral (N_plus : B)
    (h_nil : N_plus * N_plus = 0) :
    N_plus * Gamma_chiral N_plus = -N_plus := by
  dsimp [Gamma_chiral]
  rw [mul_sub, mul_add, mul_one, N_plus_mul_P N_plus h_nil, add_zero, zero_sub]

/-- **`HFD₈` Odd Chiral Parity of Supercharge `Q_+ = N_+` (`{Γ_chiral, N_+} = 0`):** -/
theorem anticomm_Gamma_chiral_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Gamma_chiral N_plus) N_plus = 0 := by
  dsimp [anticomm]
  rw [Gamma_chiral_mul_N_plus N_plus h_reg,
      N_plus_mul_Gamma_chiral N_plus h_nil,
      ← sub_eq_add_neg, sub_self]

/-- **`HFD₈` Odd Chiral Parity of Dual Supercharge `Q_- = N_-` (`{Γ_chiral, N_-} = 0`):** -/
theorem anticomm_Gamma_chiral_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    anticomm (Gamma_chiral N_plus) (star N_plus) = 0 := by
  have hL : Gamma_chiral N_plus * star N_plus = -star N_plus := by
    dsimp [Gamma_chiral]
    rw [sub_mul, add_mul, one_mul, P_mul_star_N_plus N_plus h_nil, add_zero, zero_sub]
  have hR : star N_plus * Gamma_chiral N_plus = star N_plus := by
    dsimp [Gamma_chiral]
    rw [mul_sub, mul_add, mul_one, star_N_plus_mul_P N_plus h_reg, add_sub_self_right]
  dsimp [anticomm]
  rw [hL, hR, add_comm (-star N_plus) (star N_plus), ← sub_eq_add_neg, sub_self]

/-- **`HFD₉` Emergent Poincaré Translation Equals the Higgs Bandgap (`P_poincare = V`):** -/
theorem P_poincare_eq_V (N_plus : B) : P_poincare N_plus = V N_plus := rfl

/-- **`HFD₉` SUSY Translation Invariance (`[P_poincare, Q_+] = 0`):**
    The emergent Poincaré translation generator commutes with the chiral supercharge `N_+`. -/
theorem comm_P_poincare_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (P_poincare N_plus) N_plus = 0 := by
  dsimp [comm, P_poincare, anticomm]
  have hL : (N_plus * star N_plus + star N_plus * N_plus) * N_plus = N_plus := by
    rw [add_mul, h_reg, mul_assoc (star N_plus) N_plus N_plus, h_nil, mul_zero, add_zero]
  have hR : N_plus * (N_plus * star N_plus + star N_plus * N_plus) = N_plus := by
    rw [mul_add, ← mul_assoc N_plus N_plus (star N_plus), h_nil, zero_mul,
        ← mul_assoc N_plus (star N_plus) N_plus, h_reg, zero_add]
  rw [hL, hR, sub_self]

/-- **`HFD₉` Dual SUSY Translation Invariance (`[P_poincare, Q_-] = 0`):**
    The emergent translation generator also commutes with the adjoint chiral
    supercharge `N_- = star N_plus`. -/
theorem comm_P_poincare_star_N_plus (N_plus : B)
    (h_nil : N_plus * N_plus = 0)
    (h_reg : N_plus * star N_plus * N_plus = N_plus) :
    comm (P_poincare N_plus) (star N_plus) = 0 := by
  dsimp [comm, P_poincare, anticomm]
  have hL :
      (N_plus * star N_plus + star N_plus * N_plus) * star N_plus =
        star N_plus := by
    rw [add_mul,
      mul_assoc N_plus (star N_plus) (star N_plus),
      star_N_plus_sq N_plus h_nil, mul_zero,
      star_N_plus_reg N_plus h_reg,
      zero_add]
  have hR :
      star N_plus * (N_plus * star N_plus + star N_plus * N_plus) =
        star N_plus := by
    rw [mul_add,
      ← mul_assoc (star N_plus) N_plus (star N_plus),
      star_N_plus_reg N_plus h_reg,
      ← mul_assoc (star N_plus) (star N_plus) N_plus,
      star_N_plus_sq N_plus h_nil, zero_mul, add_zero]
  rw [hL, hR, sub_self]

/-- **`HFD₁₀` Multi-Channel Supercolor Translation Closure (`[P_poincare(N_a), P_poincare(N_b)] = 0`):**
    For any two supercolor nilpotent channels `N_a, N_b` with commuting bandgap supports,
    their emergent Poincaré translation generators commute identically. -/
theorem supercolor_poincare_comm (N_a N_b : B)
    (h_comm : V N_a * V N_b = V N_b * V N_a) :
    comm (P_poincare N_a) (P_poincare N_b) = 0 := by
  dsimp [comm]
  rw [P_poincare_eq_V, P_poincare_eq_V, h_comm, sub_self]

end InfoGeometry.OperatorAlgebra.PeirceSpine.HFDArchetype
