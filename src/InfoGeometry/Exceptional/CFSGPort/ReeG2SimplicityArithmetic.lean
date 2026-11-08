/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Adapted from `CFSG.LieType.Simplicity.ReeSmall.two_mul_lt_G2`.
This arithmetic estimate is one input to the external perfectness proof for
the small Ree group of type ²G₂.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ExceptionalCatalog

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley

/-- A bounded integer expression cannot be a nonzero multiple of the large
Ree modulus. This is the generic arithmetic step used to separate a torus
commutator parameter from one in the prime field. -/
theorem not_dvd_two_mul_of_goodChar {p θ A B : ℤ} (hp : 2 ≤ p) (hθ : p ≤ θ)
    (hA : |A| ≤ p) (hB : |B| ≤ p)
    (h : (B = 0 ∧ A ≠ 0) ∨ (B ≠ 0 ∧ |A| < p))
    (hbig : 2 * (p + θ * p) < p * θ ^ 2 - 1) :
    ¬ (p * θ ^ 2 - 1) ∣ 2 * (A + θ * B) := by
  intro hd
  have hθ0 : 0 < θ := by linarith
  have hE : A + θ * B ≠ 0 := by
    rcases h with ⟨rfl, hA0⟩ | ⟨hB0, hAp⟩
    · simpa using hA0
    · intro h0
      have h1 : |θ * B| = |A| := by
        rw [show θ * B = -A by linarith, abs_neg]
      rw [abs_mul, abs_of_pos hθ0] at h1
      have hB1 : 1 ≤ |B| := Int.one_le_abs hB0
      nlinarith
  have hlt : |2 * (A + θ * B)| < p * θ ^ 2 - 1 := by
    have h1 : |A + θ * B| ≤ |A| + θ * |B| := by
      calc
        |A + θ * B| ≤ |A| + |θ * B| := abs_add_le _ _
        _ = |A| + θ * |B| := by rw [abs_mul, abs_of_pos hθ0]
    have h2 : θ * |B| ≤ θ * p := mul_le_mul_of_nonneg_left hB hθ0.le
    rw [abs_mul, abs_two]
    linarith
  have hz := Int.eq_zero_of_abs_lt_dvd hd hlt
  exact hE (by linarith)

/-- The parameter inequality used in the external ²G₂ perfectness and
quasisimplicity argument. -/
theorem two_mul_lt_ReeG2_parameter {a : ℕ} (ha : 1 ≤ a) :
    2 * ((3 : ℤ) + ((3 ^ a : ℕ) : ℤ) * 3) <
      3 * ((3 ^ a : ℕ) : ℤ) ^ 2 - 1 := by
  have h3 : (3 : ℤ) ≤ ((3 ^ a : ℕ) : ℤ) := by
    exact_mod_cast Nat.le_self_pow (by omega) 3
  nlinarith

end InfoGeometry.Exceptional.CFSGPort.Chevalley

end
