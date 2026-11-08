/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Finite-trace KMS boundary identity

The modular twist in a weighted cyclic pairing is derived directly from
cyclicity and a two-sided inverse. The operator carrier remains an arbitrary
associative, potentially noncommutative algebra; no diagonal model is used.
-/

namespace InfoGeometry.OperatorAlgebra.NoncommutativeKMSBoundary

variable {R A : Type*} [Ring A]

/-- Conjugation by the modular weight, with the order fixed by the left-weighted
trace pairing `τ (K * x)`. -/
def modularTwist (K Kinv X : A) : A := K * X * Kinv

/-- Twisted cyclicity for the left-weighted pairing `τ (K * X)`, for any cyclic
trace-like functional on the operator algebra. -/
theorem weighted_trace_kms_boundary
    (τ : A → R)
    (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    {K Kinv : A} (hK : K * Kinv = 1 ∧ Kinv * K = 1) (X Y : A) :
    τ (K * (X * Y)) = τ (K * (Y * modularTwist K Kinv X)) := by
  unfold modularTwist
  calc
    τ (K * (X * Y)) = τ ((X * Y) * K) := hτ K (X * Y)
    _ = τ (X * (Y * K)) := by rw [mul_assoc]
    _ = τ ((Y * K) * X) := hτ X (Y * K)
    _ = τ ((Kinv * K) * (Y * (K * X))) := by
      rw [hK.2, one_mul]
      simp [mul_assoc]
    _ = τ (Kinv * (K * (Y * (K * X)))) := by simp [mul_assoc]
    _ = τ ((K * (Y * (K * X))) * Kinv) := hτ Kinv (K * (Y * (K * X)))
    _ = τ (K * (Y * (K * X * Kinv))) := by simp [mul_assoc]

/-- The weighted commutator is exactly the modular defect paired against the
second operator. This is the generic noncommutative form of the KMS
commutator-defect identity. -/
theorem weighted_trace_commutator_modular_defect
    {S : Type*} [AddCommGroup S] (τ : A →+ S)
    (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    {K Kinv : A} (hK : K * Kinv = 1 ∧ Kinv * K = 1) (X Y : A) :
    τ (K * (X * Y - Y * X)) =
      τ (K * (Y * (modularTwist K Kinv X - X))) := by
  calc
    τ (K * (X * Y - Y * X)) = τ (K * (X * Y)) - τ (K * (Y * X)) := by
      rw [mul_sub, map_sub]
    _ = τ (K * (Y * modularTwist K Kinv X)) - τ (K * (Y * X)) := by
      rw [weighted_trace_kms_boundary τ hτ hK X Y]
    _ = τ (K * (Y * modularTwist K Kinv X) - K * (Y * X)) := by
      rw [map_sub]
    _ = τ (K * (Y * (modularTwist K Kinv X - X))) := by
      congr 1
      noncomm_ring

/-- A modular weight commuting with the generator is stationary for its inner
commutator, and the corresponding weighted pairing satisfies integration by
parts. -/
theorem weighted_trace_stationarity_and_integration_by_parts
    {S : Type*} [AddCommGroup S] (τ : A →+ S)
    (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    {K H : A} (hKH : K * H = H * K) (X Y : A) :
    τ (K * (H * X - X * H)) = 0 ∧
      τ (K * (X * (H * Y - Y * H))) =
        τ (K * ((X * H - H * X) * Y)) := by
  constructor
  · calc
      τ (K * (H * X - X * H)) =
          τ ((K * H) * X) - τ ((K * X) * H) := by
        rw [mul_sub, map_sub]
        simp only [mul_assoc]
      _ = τ ((H * K) * X) - τ ((K * X) * H) := by rw [hKH]
      _ = 0 := by
        have hcycle : τ ((H * K) * X) = τ ((K * X) * H) := by
          calc
            τ ((H * K) * X) = τ (H * (K * X)) := by simp only [mul_assoc]
            _ = τ ((K * X) * H) := hτ H (K * X)
        rw [hcycle]
        exact sub_self _
  · calc
      τ (K * (X * (H * Y - Y * H))) =
          τ ((K * X) * (H * Y)) - τ ((K * X) * (Y * H)) := by
        rw [← mul_assoc, mul_sub, map_sub]
      _ = τ ((K * X * H) * Y) - τ ((K * X * Y) * H) := by
        simp only [mul_assoc]
      _ = τ ((K * X * H) * Y) - τ ((H * K * X) * Y) := by
        have hcycle : τ ((K * X * Y) * H) = τ ((H * K * X) * Y) := by
          calc
            τ ((K * X * Y) * H) = τ (H * (K * X * Y)) :=
              (hτ H (K * X * Y)).symm
            _ = τ ((H * K * X) * Y) := by simp only [mul_assoc]
        rw [hcycle]
      _ = τ (K * ((X * H - H * X) * Y)) := by
        have harg :
            (K * X * H) * Y - (H * K * X) * Y =
              K * ((X * H - H * X) * Y) := by
          calc
            _ = (K * X * H) * Y - (K * H * X) * Y := by
              congr 1
              rw [← hKH]
            _ = K * ((X * H) * Y) - K * ((H * X) * Y) := by
              noncomm_ring
            _ = _ := by
              rw [← mul_sub]
              congr 1
              rw [sub_mul]
        calc
          _ = τ ((K * X * H) * Y - (H * K * X) * Y) :=
            (map_sub τ ((K * X * H) * Y) ((H * K * X) * Y)).symm
          _ = _ := congrArg τ harg

end InfoGeometry.OperatorAlgebra.NoncommutativeKMSBoundary
