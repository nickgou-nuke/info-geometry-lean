/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.JordanMultiplicationClosure
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Lie and Jordan multiplication on an associative algebra

The adjoint action is Mathlib's `LieAlgebra.ad`; unnormalized Jordan
multiplication is the existing `JordanMultiplicationClosure.jordanLeft`.
Their sum and difference are native linear endomorphisms. Both ordered
products retain the mixed commutator, without requiring the coefficients
to commute. Only the converse commutation criterion needs injective doubling.

The trace statements use a cyclic additive functional and its biadditive
pairing. They make no positivity, connection, or state-dependent metric claim.
-/

namespace InfoGeometry.Core.LieJordanComposition

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.JordanMultiplicationClosure

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The mixed Lie/Jordan identity as an equality of native endomorphisms. -/
theorem ad_jordan_bracket (h s : A) :
    ⁅LieAlgebra.ad R A h, jordanLeft (R := R) s⁆ =
      jordanLeft (R := R) ⁅h, s⁆ := by
  apply LinearMap.ext
  intro x
  exact InfoGeometry.Core.JordanAssociator.commutator_symm_operator h s x

/-- The Jordan/Jordan bracket has the coefficient order `[h,s]`. -/
theorem jordan_jordan_bracket (h s : A) :
    ⁅jordanLeft (R := R) h, jordanLeft (R := R) s⁆ =
      LieAlgebra.ad R A ⁅h, s⁆ := by
  apply LinearMap.ext
  intro x
  exact InfoGeometry.Core.JordanAssociator.symm_operator_commutator h s x

/-- The sum of the native adjoint action and the existing Jordan action. -/
def plus (h s : A) : Module.End R A :=
  LieAlgebra.ad R A h + jordanLeft (R := R) s

/-- The difference of the native adjoint action and the existing Jordan action. -/
def minus (h s : A) : Module.End R A :=
  LieAlgebra.ad R A h - jordanLeft (R := R) s

@[simp] theorem plus_apply (h s x : A) :
    plus (R := R) h s x = h * x - x * h + (s * x + x * s) := rfl

@[simp] theorem minus_apply (h s x : A) :
    minus (R := R) h s x = h * x - x * h - (s * x + x * s) := rfl

theorem plus_add_minus (h s : A) :
    plus (R := R) h s + minus (R := R) h s =
      2 • LieAlgebra.ad R A h := by
  simp only [plus, minus, two_nsmul]
  abel

theorem plus_sub_minus (h s : A) :
    plus (R := R) h s - minus (R := R) h s =
      2 • jordanLeft (R := R) s := by
  simp only [plus, minus, two_nsmul]
  abel

/-- Minus after plus has the positive mixed correction. -/
theorem minus_mul_plus (h s : A) :
    minus (R := R) h s * plus (R := R) h s =
      LieAlgebra.ad R A h * LieAlgebra.ad R A h -
        jordanLeft (R := R) s * jordanLeft (R := R) s +
          jordanLeft (R := R) ⁅h, s⁆ := by
  rw [← ad_jordan_bracket (R := R) h s]
  change (LieAlgebra.ad R A h - jordanLeft (R := R) s) *
      (LieAlgebra.ad R A h + jordanLeft (R := R) s) =
    LieAlgebra.ad R A h * LieAlgebra.ad R A h -
      jordanLeft (R := R) s * jordanLeft (R := R) s +
        (LieAlgebra.ad R A h * jordanLeft (R := R) s -
          jordanLeft (R := R) s * LieAlgebra.ad R A h)
  noncomm_ring

/-- Plus after minus has the negative mixed correction. -/
theorem plus_mul_minus (h s : A) :
    plus (R := R) h s * minus (R := R) h s =
      LieAlgebra.ad R A h * LieAlgebra.ad R A h -
        jordanLeft (R := R) s * jordanLeft (R := R) s -
          jordanLeft (R := R) ⁅h, s⁆ := by
  rw [← ad_jordan_bracket (R := R) h s]
  change (LieAlgebra.ad R A h + jordanLeft (R := R) s) *
      (LieAlgebra.ad R A h - jordanLeft (R := R) s) =
    LieAlgebra.ad R A h * LieAlgebra.ad R A h -
      jordanLeft (R := R) s * jordanLeft (R := R) s -
        (LieAlgebra.ad R A h * jordanLeft (R := R) s -
          jordanLeft (R := R) s * LieAlgebra.ad R A h)
  noncomm_ring

/-- Adding the two ordered products cancels the mixed correction. -/
theorem ordered_products_add (h s : A) :
    minus (R := R) h s * plus (R := R) h s +
      plus (R := R) h s * minus (R := R) h s =
        2 • (LieAlgebra.ad R A h * LieAlgebra.ad R A h -
          jordanLeft (R := R) s * jordanLeft (R := R) s) := by
  rw [minus_mul_plus, plus_mul_minus, two_nsmul]
  abel

/-- Their ordered difference records twice the full mixed correction. -/
theorem ordered_products_sub (h s : A) :
    minus (R := R) h s * plus (R := R) h s -
      plus (R := R) h s * minus (R := R) h s =
        2 • jordanLeft (R := R) ⁅h, s⁆ := by
  rw [minus_mul_plus, plus_mul_minus, two_nsmul]
  abel

/-- Commutation of the two endomorphisms detects coefficient commutation
when doubling is injective. Evaluation at `1` requires two cancellations. -/
theorem plus_minus_commute_iff
    (h2 : Function.Injective (fun a : A => (2 : ℕ) • a)) (h s : A) :
    Commute (plus (R := R) h s) (minus (R := R) h s) ↔ Commute h s := by
  constructor
  · intro hc
    have hz : 2 • jordanLeft (R := R) ⁅h, s⁆ = 0 := by
      rw [← ordered_products_sub (R := R) h s]
      exact sub_eq_zero.mpr hc.eq.symm
    have hv := congrArg (fun f : Module.End R A => f 1) hz
    rw [LinearMap.smul_apply] at hv
    change 2 • (⁅h, s⁆ * 1 + 1 * ⁅h, s⁆) = 0 at hv
    rw [mul_one, one_mul] at hv
    have hdouble : ⁅h, s⁆ + ⁅h, s⁆ = 0 := by
      apply h2
      simpa only [smul_zero] using hv
    have hsingle : ⁅h, s⁆ = 0 := by
      apply h2
      simpa only [two_nsmul, add_zero] using hdouble
    change h * s = s * h
    exact sub_eq_zero.mp hsingle
  · intro hc
    have hb : ⁅h, s⁆ = 0 := sub_eq_zero.mpr hc.eq
    have hj : jordanLeft (R := R) ⁅h, s⁆ = 0 := by
      apply LinearMap.ext
      intro x
      change ⁅h, s⁆ * x + x * ⁅h, s⁆ = 0
      rw [hb]
      simp
    change plus (R := R) h s * minus (R := R) h s =
      minus (R := R) h s * plus (R := R) h s
    rw [plus_mul_minus, minus_mul_plus, hj, sub_zero, add_zero]

section CyclicTrace

variable {G : Type*} [AddCommGroup G]
    (τ : A →+ G) (hτ : ∀ x y : A, τ (x * y) = τ (y * x))

include hτ

/-- The native adjoint action is skew for the cyclic biadditive pairing. -/
theorem trace_ad_skew (h x y : A) :
    τ (LieAlgebra.ad R A h x * y) + τ (x * LieAlgebra.ad R A h y) = 0 := by
  change τ ((h * x - x * h) * y) + τ (x * (h * y - y * h)) = 0
  simpa only [add_comm] using
    (InfoGeometry.Core.JordanMultiplicationClosure.trace_adjoint_identity τ hτ h x y)

/-- Jordan multiplication is symmetric for the same cyclic biadditive pairing. -/
theorem trace_jordan_symmetric (s x y : A) :
    τ (jordanLeft (R := R) s x * y) = τ (x * jordanLeft (R := R) s y) := by
  change τ ((s * x + x * s) * y) = τ (x * (s * y + y * s))
  have hcyclic : τ (s * x * y) = τ (x * (y * s)) := by
    rw [mul_assoc s x y, hτ s (x * y), mul_assoc x y s]
  rw [add_mul, mul_add, map_add, map_add, hcyclic, mul_assoc x s y]
  exact add_comm _ _

/-- The sum and difference are negative adjoints for the cyclic pairing. -/
theorem trace_plus_minus (h s x y : A) :
    τ (plus (R := R) h s x * y) + τ (x * minus (R := R) h s y) = 0 := by
  change τ ((LieAlgebra.ad R A h x + jordanLeft (R := R) s x) * y) +
    τ (x * (LieAlgebra.ad R A h y - jordanLeft (R := R) s y)) = 0
  rw [add_mul, mul_sub, map_add, map_sub, trace_jordan_symmetric τ hτ s x y]
  calc
    _ = τ (LieAlgebra.ad R A h x * y) + τ (x * LieAlgebra.ad R A h y) := by
      abel
    _ = 0 := trace_ad_skew τ hτ h x y

/-- The reverse adjunction uses the same pairing and no extra hypotheses. -/
theorem trace_minus_plus (h s x y : A) :
    τ (minus (R := R) h s x * y) + τ (x * plus (R := R) h s y) = 0 := by
  change τ ((LieAlgebra.ad R A h x - jordanLeft (R := R) s x) * y) +
    τ (x * (LieAlgebra.ad R A h y + jordanLeft (R := R) s y)) = 0
  rw [sub_mul, mul_add, map_sub, map_add, trace_jordan_symmetric τ hτ s x y]
  calc
    _ = τ (LieAlgebra.ad R A h x * y) + τ (x * LieAlgebra.ad R A h y) := by
      abel
    _ = 0 := trace_ad_skew τ hτ h x y

/-- Exact trace shift of the sum, without a nonvanishing or positivity claim. -/
theorem trace_plus (h s x : A) :
    τ (plus (R := R) h s x) = 2 • τ (s * x) := by
  rw [plus_apply, map_add,
    InfoGeometry.Core.JordanAssociator.trace_commutator τ hτ h x,
    InfoGeometry.Core.JordanAssociator.trace_symm τ hτ s x, zero_add]

/-- Exact opposite trace shift of the difference. -/
theorem trace_minus (h s x : A) :
    τ (minus (R := R) h s x) = -(2 • τ (s * x)) := by
  rw [minus_apply, map_sub,
    InfoGeometry.Core.JordanAssociator.trace_commutator τ hτ h x,
    InfoGeometry.Core.JordanAssociator.trace_symm τ hτ s x, zero_sub]

end CyclicTrace

end InfoGeometry.Core.LieJordanComposition
