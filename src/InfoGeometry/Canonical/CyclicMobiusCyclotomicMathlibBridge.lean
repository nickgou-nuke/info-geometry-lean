/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cyclotomic24MathlibBridge
import InfoGeometry.Canonical.KantorTanakaFiveGradedMetriplecticZornPoset

/-!
# Mathlib cyclotomic identification for the cyclic Möbius RN stage

This bridge identifies the finite polynomial used by the RN5 owner with
Mathlib's canonical cyclotomic polynomial after evaluation. It does not assert
an analytic Dirichlet-series identity or identify arithmetic Möbius inversion
with the projective chart transition.
-/

namespace InfoGeometry.Canonical.CyclicMobiusCyclotomicMathlibBridge

open Polynomial
open InfoGeometry.Canonical.KantorTanakaFiveGradedMetriplecticZornPoset

/-- Evaluating the RN5 explicit polynomial is evaluation of Mathlib's native
24th cyclotomic polynomial, with the integer coefficients mapped into `R`. -/
theorem eval_cyclotomic24_eq_rn5Poly {R : Type*} [CommRing R] (x : R) :
    Polynomial.eval₂ (Int.castRingHom R) x (Polynomial.cyclotomic 24 ℤ) =
      CyclicMobiusRingNibelung.phi24Poly x := by
  rw [InfoGeometry.Canonical.Cyclotomic24MathlibBridge.cyclotomic24_eq_explicit]
  simp [InfoGeometry.Canonical.Cyclotomic24MathlibBridge.phi24Explicit,
    CyclicMobiusRingNibelung.phi24Poly]

/-- The RN5 division-free factorization is therefore the corresponding
Mathlib-cyclotomic evaluation identity. -/
theorem eval_cyclotomic24_divisor_factorization {R : Type*} [CommRing R] (x : R) :
    (x ^ 12 - 1) * (x ^ 8 - 1) *
      Polynomial.eval₂ (Int.castRingHom R) x (Polynomial.cyclotomic 24 ℤ) =
        (x ^ 24 - 1) * (x ^ 4 - 1) := by
  rw [eval_cyclotomic24_eq_rn5Poly]
  dsimp [CyclicMobiusRingNibelung.phi24Poly]
  ring

/-- The RN5 polynomial is also Mathlib's Möbius-weighted divisor product at
24, interpreted in the fraction field of `ℤ[X]`. This is the finite
cyclotomic inversion statement; it asserts no Dirichlet-series identity. -/
theorem phi24Explicit_eq_moebius_divisor_product :
    algebraMap ℤ[X] (RatFunc ℤ)
        InfoGeometry.Canonical.Cyclotomic24MathlibBridge.phi24Explicit =
      ∏ i ∈ (24 : ℕ).divisorsAntidiagonal,
        algebraMap ℤ[X] (RatFunc ℤ) (X ^ i.snd - 1) ^
          ArithmeticFunction.moebius i.fst := by
  rw [← InfoGeometry.Canonical.Cyclotomic24MathlibBridge.cyclotomic24_eq_explicit]
  exact Polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius (n := 24) ℤ

end InfoGeometry.Canonical.CyclicMobiusCyclotomicMathlibBridge
