/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.JordanAssociatorRing
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Basic

/-!
# Commutators of unnormalized Jordan multiplication operators

This is an associative-envelope identity. It is not a construction or
classification of the exceptional Lie algebras F4 or E6. The source note's
final nested-commutator order is corrected explicitly.
-/

namespace InfoGeometry.Core.JordanMultiplicationClosure

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Native linear left multiplication for the unnormalized Jordan product. -/
def jordanLeft (s : A) : Module.End R A where
  toFun x := s * x + x * s
  map_add' x y := by simp only [mul_add, add_mul]; abel
  map_smul' r x := by simp only [mul_smul_comm, smul_mul_assoc, smul_add]

/-- The commutator order is `[s,t]`, not `[t,s]`. -/
theorem commutator_apply (s t x : A) :
    (jordanLeft (R := R) s * jordanLeft t - jordanLeft t * jordanLeft s) x =
      (s * t - t * s) * x - x * (s * t - t * s) := by
  change s * (t * x + x * t) + (t * x + x * t) * s -
    (t * (s * x + x * s) + (s * x + x * s) * t) = _
  noncomm_ring

/-- The associator orientation from the note agrees with the corrected bracket. -/
theorem associator_orientation (s t x : A) :
    ((t * x + x * t) * s + s * (t * x + x * t)) -
      (t * (x * s + s * x) + (x * s + s * x) * t) =
        (s * t - t * s) * x - x * (s * t - t * s) := by
  rw [InfoGeometry.Core.JordanAssociator.symm_associator_eq_double_commutator]
  noncomm_ring

/-- The resulting linear operator obeys the associative Leibniz identity. -/
theorem commutator_leibniz (s t x y : A) :
    (jordanLeft (R := R) s * jordanLeft t - jordanLeft t * jordanLeft s) (x * y) =
      ((jordanLeft (R := R) s * jordanLeft t - jordanLeft t * jordanLeft s) x) * y +
      x * ((jordanLeft (R := R) s * jordanLeft t - jordanLeft t * jordanLeft s) y) := by
  simp only [commutator_apply]
  noncomm_ring

/-- With a cyclic additive trace the inner action is trace-skew; no dual-space
identification or nondegeneracy is assumed. -/
theorem trace_adjoint_identity {G : Type*} [AddCommGroup G]
    (τ : A →+ G) (hτ : ∀ x y : A, τ (x * y) = τ (y * x)) (l ξ x : A) :
    τ (ξ * (l * x - x * l)) + τ ((l * ξ - ξ * l) * x) = 0 := by
  rw [← map_add]
  have he : ξ * (l * x - x * l) + (l * ξ - ξ * l) * x =
      l * (ξ * x) - (ξ * x) * l := by noncomm_ring
  rw [he, map_sub, hτ l (ξ * x), sub_self]

end InfoGeometry.Core.JordanMultiplicationClosure
