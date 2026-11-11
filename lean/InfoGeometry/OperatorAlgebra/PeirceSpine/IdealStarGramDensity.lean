/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentCornerEndEquivalence
import InfoGeometry.Core.IdempotencyDefect
import Mathlib.Algebra.Star.Basic

/-!
# Principal-ideal star support, Gram pairings, and density defects

The carrier is an arbitrary associative star ring. Star reverses the side of
ideal support without requiring a self-adjoint idempotent. The pairing has
rectangular support `star p * B * p`; vanishing of every pairing on the ideal
is equivalent to vanishing of every such sandwich.

Density powers and the idempotency defect retain the ordered Gram factor.
Normalization is sufficient for idempotence, and an explicit right-unitary
condition preserves density. These identities assert neither positivity nor
a bijection between ideal generators and idempotent densities.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B] [StarRing B]

/-- Star exchanges right support by `p` with left support by `star p`. -/
theorem right_support_iff_star_left_support (p x : B) :
    x * p = x ↔ star p * star x = star x := by
  constructor
  · intro h
    simpa only [star_mul] using congrArg star h
  · intro h
    simpa only [star_mul, star_star] using congrArg star h

/-- Native ideal membership has the same dual-support characterization; no
self-adjointness assumption on the idempotent is used. -/
theorem mem_idempotentLeftIdeal_iff_star_left_support
    (p : B) (hp : p * p = p) (x : B) :
    x ∈ idempotentLeftIdeal p hp ↔ star p * star x = star x := by
  change x * p = x ↔ star p * star x = star x
  exact right_support_iff_star_left_support p x

/-- The Gram pairing has rectangular support, even when `star p ≠ p`. -/
theorem ideal_gram_rectangular_support {p φ ψ : B}
    (hφ : φ * p = φ) (hψ : ψ * p = ψ) :
    star p * (star φ * ψ) * p = star φ * ψ := by
  have hφs : star p * star φ = star φ :=
    (right_support_iff_star_left_support p φ).mp hφ
  calc
    star p * (star φ * ψ) * p =
        (star p * star φ) * (ψ * p) := by simp only [mul_assoc]
    _ = star φ * ψ := by rw [hφs, hψ]

/-- Every pairing on the whole ideal vanishes exactly when all rectangular
sandwiches vanish. This is a statement about all pairs, not merely about
the diagonal Gram values. -/
theorem idempotentLeftIdeal_pairing_zero_iff
    (p : B) (hp : p * p = p) :
    (∀ φ ψ : idempotentLeftIdeal p hp, star (φ : B) * (ψ : B) = 0) ↔
      ∀ a : B, star p * a * p = 0 := by
  constructor
  · intro h a
    have hpp : p ∈ idempotentLeftIdeal p hp := hp
    have hpa : a * p ∈ idempotentLeftIdeal p hp := by
      change (a * p) * p = a * p
      rw [mul_assoc, hp]
    have hpair := h ⟨p, hpp⟩ ⟨a * p, hpa⟩
    change star p * (a * p) = 0 at hpair
    simpa only [mul_assoc] using hpair
  · intro h φ ψ
    have hφ : (φ : B) * p = (φ : B) := φ.property
    have hψ : (ψ : B) * p = (ψ : B) := ψ.property
    calc
      star (φ : B) * (ψ : B) =
          star p * (star (φ : B) * (ψ : B)) * p :=
        (ideal_gram_rectangular_support hφ hψ).symm
      _ = 0 := h (star (φ : B) * (ψ : B))

/-- Every positive density power keeps the ordered Gram factor in the middle.
This is the native monoid transport identity `mul_pow_mul`. -/
theorem star_density_pow_succ (ψ : B) (n : ℕ) :
    (ψ * star ψ) ^ (n + 1) = ψ * (star ψ * ψ) ^ n * star ψ := by
  rw [pow_succ, ← mul_assoc, mul_pow_mul]

/-- The ambient idempotency defect factors through the Gram value minus `1`. -/
theorem star_density_defect (ψ : B) :
    InfoGeometry.Core.IdempotencyDefect.defect (ψ * star ψ) =
      ψ * (star ψ * ψ - 1) * star ψ := by
  simp only [InfoGeometry.Core.IdempotencyDefect.defect,
    mul_sub, sub_mul, mul_one, mul_assoc]

/-- For an ideal-supported generator, the support idempotent replaces the
ambient unit in the exact density defect. -/
theorem ideal_star_density_defect {p ψ : B} (hψ : ψ * p = ψ) :
    InfoGeometry.Core.IdempotencyDefect.defect (ψ * star ψ) =
      ψ * (star ψ * ψ - p) * star ψ := by
  calc
    InfoGeometry.Core.IdempotencyDefect.defect (ψ * star ψ) =
        ψ * (star ψ * ψ - 1) * star ψ := star_density_defect ψ
    _ = ψ * (star ψ * ψ - p) * star ψ := by
      simp only [mul_sub, mul_one, sub_mul, hψ]

/-- Normalization to the support is sufficient for idempotent density. -/
theorem ideal_star_density_idempotent_of_normalized {p ψ : B}
    (hψ : ψ * p = ψ) (hN : star ψ * ψ = p) :
    IsIdempotentElem (ψ * star ψ) := by
  apply (InfoGeometry.Core.IdempotencyDefect.defect_eq_zero_iff _).mp
  rw [ideal_star_density_defect hψ, hN, sub_self, mul_zero, zero_mul]

/-- Right multiplication acts on the Gram value by ordered star congruence. -/
theorem star_gram_right_mul (ψ u : B) :
    star (ψ * u) * (ψ * u) = star u * (star ψ * ψ) * u := by
  simp only [star_mul, mul_assoc]

/-- The density depends on the right multiplier through `u * star u`. -/
theorem star_density_right_mul (ψ u : B) :
    (ψ * u) * star (ψ * u) = ψ * (u * star u) * star ψ := by
  simp only [star_mul, mul_assoc]

/-- The right-unitary range equation relative to the support preserves
density. Only the displayed one-sided equation is needed. -/
theorem ideal_star_density_right_mul_eq {p ψ u : B}
    (hψ : ψ * p = ψ) (hu : u * star u = p) :
    (ψ * u) * star (ψ * u) = ψ * star ψ := by
  rw [star_density_right_mul, hu, hψ]

/-- If the support annihilates its star in this order, every supported
generator has zero density. The reversed annihilation equation is not used. -/
theorem ideal_star_density_eq_zero_of_mul_star_eq_zero {p ψ : B}
    (hψ : ψ * p = ψ) (hpstar : p * star p = 0) :
    ψ * star ψ = 0 := by
  have hψs : star p * star ψ = star ψ :=
    (right_support_iff_star_left_support p ψ).mp hψ
  calc
    ψ * star ψ = (ψ * p) * (star p * star ψ) := by rw [hψ, hψs]
    _ = ψ * (p * star p) * star ψ := by simp only [mul_assoc]
    _ = 0 := by rw [hpstar, mul_zero, zero_mul]

/-- In the same regime the Gram value is square-zero; this does not assert
that the Gram value itself vanishes. -/
theorem ideal_gram_sq_eq_zero_of_mul_star_eq_zero {p ψ : B}
    (hψ : ψ * p = ψ) (hpstar : p * star p = 0) :
    (star ψ * ψ) ^ 2 = 0 := by
  have hρ := ideal_star_density_eq_zero_of_mul_star_eq_zero hψ hpstar
  calc
    (star ψ * ψ) ^ 2 = star ψ * (ψ * star ψ) * ψ := by
      simp only [pow_two, mul_assoc]
    _ = 0 := by rw [hρ, mul_zero, zero_mul]

/-- A complementary star of an idempotent supplies the ordered
annihilation hypothesis used by the preceding density and Gram theorems. -/
theorem mul_star_eq_zero_of_star_eq_one_sub {p : B}
    (hp : p * p = p) (hstar : star p = 1 - p) :
    p * star p = 0 := by
  rw [hstar]
  exact (show IsIdempotentElem p from hp).mul_one_sub_self

end InfoGeometry.OperatorAlgebra.PeirceSpine
