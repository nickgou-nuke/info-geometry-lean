/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Tactic

/-!
# Custodial exchange selection rule

This file isolates the noncommutative algebraic content of an involutive
exchange symmetry.  An element `P` is fixed on both sides by an involution
`W`; two insertions commute with `W`, while an odd insertion anticommutes
with it.  The resulting fixed-sector sandwich vanishes in any 2-torsion-free ring.  No
commutativity of the coefficient algebra or scalar/diagonal model is used.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Even powers of an element anticommuting with `W` commute with `W`. -/
theorem exchange_commutes_even_power (W X : B) (hWX : W * X = -X * W) :
    ∀ n : ℕ, W * X ^ (2 * n) = X ^ (2 * n) * W := by
  have hWXX : W * (X * X) = (X * X) * W := by
    calc
      W * (X * X) = (W * X) * X := by rw [mul_assoc]
      _ = (-X * W) * X := by rw [hWX]
      _ = -X * (W * X) := by noncomm_ring
      _ = -X * (-X * W) := by rw [hWX]
      _ = (X * X) * W := by noncomm_ring
  have hpow : ∀ n : ℕ, W * (X * X) ^ n = (X * X) ^ n * W := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        calc
          W * ((X * X) ^ n * (X * X)) = (W * (X * X) ^ n) * (X * X) := by rw [mul_assoc]
          _ = ((X * X) ^ n * W) * (X * X) := by rw [ih]
          _ = (X * X) ^ n * (W * (X * X)) := by noncomm_ring
          _ = (X * X) ^ n * ((X * X) * W) := by rw [hWXX]
          _ = (X * X) ^ n * (X * X) * W := by noncomm_ring
  intro n
  have h := hpow n
  have hp : X ^ (2 * n) = (X ^ 2) ^ n := pow_mul X 2 n
  rw [hp, pow_two]
  exact h

/-- Odd powers of an element anticommuting with `W` still anticommute with `W`. -/
theorem exchange_anticommutes_odd_power (W X : B) (hWX : W * X = -X * W) :
    ∀ n : ℕ, W * X ^ (2 * n + 1) = -(X ^ (2 * n + 1)) * W := by
  intro n
  have heven := exchange_commutes_even_power W X hWX n
  rw [pow_succ]
  calc
    W * (X ^ (2 * n) * X) = (W * X ^ (2 * n)) * X := by rw [mul_assoc]
    _ = (X ^ (2 * n) * W) * X := by rw [heven]
    _ = X ^ (2 * n) * (W * X) := by noncomm_ring
    _ = X ^ (2 * n) * (-X * W) := by rw [hWX]
    _ = -(X ^ (2 * n) * X) * W := by noncomm_ring

/--
All odd insertions vanish in a sandwich supported on the fixed sector of an involution.

The assumptions record the exact algebraic interface: `W` is involutive,
`P` is fixed on both sides by `W`, `A` and `C` commute with `W`, and `X`
anticommutes with it.  The last hypothesis is discharged for odd powers by
`exchange_anticommutes_odd_power`.  The explicit 2-torsion-freeness condition
is necessary over a general ring; it is not silently replaced by a field.
-/
theorem custodial_corner_odd_sandwich_eq_zero
    (W P A X C : B)
    (hW : W * W = 1)
    (hWP : W * P = P) (hPW : P * W = P)
    (hAW : W * A = A * W) (hCW : W * C = C * W)
    (hWX : W * X = -X * W)
    (h2 : ∀ z : B, z + z = 0 → z = 0) :
    P * A * X * C * P = 0 := by
  let Y : B := P * A * X * C * P
  have hleft : W * Y = Y := by
    dsimp [Y]
    calc
      W * (P * A * X * C * P) = (W * P) * A * X * C * P := by noncomm_ring
      _ = P * A * X * C * P := by rw [hWP]
  have hright : Y * W = Y := by
    dsimp [Y]
    calc
      (P * A * X * C * P) * W = P * A * X * C * (P * W) := by noncomm_ring
      _ = P * A * X * C * P := by rw [hPW]
  have hleft' : W * Y = -Y := by
    calc
      W * Y = Y := hleft
      _ = Y * W := hright.symm
      _ = W * Y * W := by rw [hleft]
      _ = -(P * A * X * C * P) := by
        have hconjP : W * P * W = P := by rw [hWP, hPW]
        have hconjA : W * A * W = A := by
          calc W * A * W = A * W * W := by rw [hAW]
            _ = A * (W * W) := by noncomm_ring
            _ = A := by rw [hW, mul_one]
        have hconjC : W * C * W = C := by
          calc W * C * W = C * W * W := by rw [hCW]
            _ = C * (W * W) := by noncomm_ring
            _ = C := by rw [hW, mul_one]
        have hconjX : W * X * W = -X := by
          calc W * X * W = -X * W * W := by rw [hWX]
            _ = -X * (W * W) := by noncomm_ring
            _ = -X := by rw [hW, mul_one]
        have hconjMul : ∀ a b : B, W * (a * b) * W = (W * a * W) * (W * b * W) := by
          intro a b
          calc
            W * (a * b) * W = W * a * (W * W) * b * W := by
              rw [hW]
              noncomm_ring
            _ = (W * a * W) * (W * b * W) := by noncomm_ring
        have hconj5 : ∀ a b c d e : B,
            W * (a * b * c * d * e) * W =
              (W * a * W) * (W * b * W) * (W * c * W) * (W * d * W) * (W * e * W) := by
          intro a b c d e
          calc
            W * (a * b * c * d * e) * W =
                (W * (a * b * c * d) * W) * (W * e * W) := hconjMul (a * b * c * d) e
            _ = ((W * a * W) * (W * b * W) * (W * c * W) * (W * d * W)) * (W * e * W) := by
                rw [hconjMul (a * b * c) d, hconjMul (a * b) c, hconjMul a b]
        calc
          W * (P * A * X * C * P) * W =
              (W * P * W) * (W * A * W) * (W * X * W) * (W * C * W) * (W * P * W) :=
            hconj5 P A X C P
          _ = -(P * A * X * C * P) := by
            simp only [hconjP, hconjA, hconjX, hconjC]
            noncomm_ring
  have hzero : Y + Y = 0 := by
    have hEq : Y = -Y := by
      calc Y = W * Y := hleft.symm
        _ = -Y := hleft'
    have hcongr := congrArg (fun z : B => z + Y) hEq
    simpa using hcongr
  have : Y = 0 := h2 Y hzero
  simpa [Y] using this

/-- Odd-power insertion form of the custodial selection rule. -/
theorem custodial_corner_odd_power_sandwich_eq_zero
    (W P A X C : B) (n : ℕ)
    (hW : W * W = 1)
    (hWP : W * P = P) (hPW : P * W = P)
    (hAW : W * A = A * W) (hCW : W * C = C * W)
    (hWX : W * X = -X * W)
    (h2 : ∀ z : B, z + z = 0 → z = 0) :
    P * A * X ^ (2 * n + 1) * C * P = 0 := by
  apply custodial_corner_odd_sandwich_eq_zero W P A (X ^ (2 * n + 1)) C hW hWP hPW hAW hCW
    (exchange_anticommutes_odd_power W X hWX n) h2

end InfoGeometry.OperatorAlgebra.PeirceSpine
