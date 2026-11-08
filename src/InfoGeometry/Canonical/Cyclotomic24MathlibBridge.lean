/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# Native Mathlib bridge for the explicit 24th cyclotomic polynomial

This file identifies the explicit integer polynomial used in the finite
Möbius/cyclotomic owners with Mathlib's canonical `Polynomial.cyclotomic`.
The proof uses the native prime-expansion identity twice, starting from
Mathlib's explicit sixth cyclotomic polynomial. It makes no analytic or
geometric identification between arithmetic and projective Möbius maps.
-/

namespace InfoGeometry.Canonical.Cyclotomic24MathlibBridge

open Polynomial

/-- The explicit integer polynomial occurring in the repository's `Phi₂₄`
factorization identities. -/
noncomputable def phi24Explicit : ℤ[X] := X ^ 8 - X ^ 4 + 1

/-- Mathlib's canonical 24th cyclotomic polynomial is `X⁸ - X⁴ + 1`. -/
theorem cyclotomic24_eq_explicit : Polynomial.cyclotomic 24 ℤ = phi24Explicit := by
  rw [show (24 : ℕ) = 12 * 2 by norm_num,
    ← Polynomial.cyclotomic_expand_eq_cyclotomic Nat.prime_two (by norm_num) ℤ,
    show (12 : ℕ) = 6 * 2 by norm_num,
    ← Polynomial.cyclotomic_expand_eq_cyclotomic Nat.prime_two (by norm_num) ℤ,
    Polynomial.cyclotomic_six]
  simp [phi24Explicit, Polynomial.expand_X]
  ring

/-- The same explicit identification holds after mapping integer coefficients
into any ring. -/
theorem map_cyclotomic24_eq_explicit (R : Type*) [Ring R] :
    Polynomial.cyclotomic 24 R = Polynomial.map (Int.castRingHom R) phi24Explicit := by
  rw [← Polynomial.map_cyclotomic_int, cyclotomic24_eq_explicit]

/-- Over any commutative ring, evaluation of Mathlib's canonical polynomial
is the explicit scalar polynomial used by the repository's 24-cyclotomic
archetypes. -/
theorem eval_cyclotomic24_eq_explicit {R : Type*} [CommRing R] (x : R) :
    (Polynomial.cyclotomic 24 R).eval x = x ^ 8 - x ^ 4 + 1 := by
  rw [map_cyclotomic24_eq_explicit]
  simp [phi24Explicit]

end InfoGeometry.Canonical.Cyclotomic24MathlibBridge
