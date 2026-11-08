/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.JordanAssociator

/-!
# The normalized Jordan associator of a square-zero inner-inverse pair

For an associative real algebra `A`, the repository uses the normalized special
Jordan product

`x ∘ y = (1 / 2) • (x * y + y * x)`.

If `d * d = 0` and `d * B * d = d`, then

`(d ∘ d) ∘ B - d ∘ (d ∘ B) = -(1 / 2) • d`.

This is the normalized-envelope form of the often-quoted unnormalized identity
`-2 • d`: the factor differs because the unnormalized product `x * y + y * x`
is twice the normalized one.  The statement uses only the inner-inverse law, not
the full Moore--Penrose or Drazin hypotheses.
-/

namespace InfoGeometry.Core.JordanAssociator

open InfoGeometry.Core.JordanPeirceDecomposition

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The normalized special-Jordan associator of a square-zero element with an
inner inverse is `-(1/2) • d`. -/
theorem jordan_associator_square_zero_inner_inverse {d B : A}
    (hd : d * d = 0) (hinner : d * B * d = d) :
    jordanMul (jordanMul d d) B - jordanMul d (jordanMul d B) =
      -(1 / 2 : ℝ) • d := by
  have hdd : jordanMul d d = 0 := by
    simp [jordanMul, hd]
  have h0 : jordanMul (0 : A) B = 0 := by
    simp [jordanMul]
  have hcomm :=
    jordan_associator_eq_expanded_double_commutator (x := d) (y := d) (z := B)
  have hcomm_expand :
      d * (d * B - B * d) - (d * B - B * d) * d = -(2 : ℝ) • d := by
    calc
      d * (d * B - B * d) - (d * B - B * d) * d =
          (d * d) * B - (d * B) * d - (d * B) * d + (B * d) * d := by
            noncomm_ring
      _ = -(2 : ℝ) • d := by
            rw [hd, hinner, mul_assoc B d d, hd, mul_zero]
            norm_num
            module
  rw [hdd, h0] at hcomm
  rw [hcomm_expand] at hcomm
  have hscalar : (1 / 4 : ℝ) • (-(2 : ℝ) • d) = -(1 / 2 : ℝ) • d := by
    rw [smul_smul]
    norm_num
  rw [hscalar] at hcomm
  rw [hdd, h0]
  exact hcomm

end InfoGeometry.Core.JordanAssociator
