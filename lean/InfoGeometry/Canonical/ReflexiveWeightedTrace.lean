/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveMatrixCorner
import InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance

/-!
# Weighted support operators and cyclic linear functionals

Contract: central scalar weights in an associative algebra, with a cyclic
`R`-linear functional. The weighted-support operator is the image of a diagonal
matrix under the existing matrix representation. The resulting balance laws
assert neither positivity nor normalization nor an analytic KMS condition.
-/
namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows
open UnifiedGeometryOperatorSignificance

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The two weights have the same ordering as the existing support owner. -/
theorem pairMatrixLinear_weight (d B : A) (u v : R) :
    pairMatrixLinear d B (!![v * v, 0; 0, u * u] : Matrix (Fin 2) (Fin 2) R) =
      kmsModularWeight u v d B := by
  simp [pairMatrixLinear_apply, pairMatrixUnit, kmsModularWeight, projPlus, projMinus,
    add_comm]

/-- Transport a weighted operator identity through a cyclic linear functional. -/
theorem cyclic_weighted_balance (τ : A →ₗ[R] R)
    (hcyclic : ∀ x y : A, τ (x * y) = τ (y * x))
    (a b : R) (ρ x Y : A) (h : a • (ρ * x) = b • (x * ρ)) :
    a * τ (ρ * (x * Y)) = b * τ (ρ * (Y * x)) := by
  have ht := congrArg (fun z : A => τ (z * Y)) h
  simp only [smul_mul_assoc, map_smul, smul_eq_mul] at ht
  calc
    a * τ (ρ * (x * Y)) = b * τ ((x * ρ) * Y) := by
      simpa only [mul_assoc] using ht
    _ = b * τ (ρ * (Y * x)) := by
      rw [mul_assoc x ρ Y, hcyclic x (ρ * Y), mul_assoc ρ Y x]

theorem cyclic_support_balance_d (τ : A →ₗ[R] R)
    (hcyclic : ∀ x y : A, τ (x * y) = τ (y * x))
    {d B : A} (hd : d * d = 0) (hr : d * B * d = d) (u v : R) (Y : A) :
    (u * u) * τ (kmsModularWeight u v d B * (d * Y)) =
      (v * v) * τ (kmsModularWeight u v d B * (Y * d)) :=
  cyclic_weighted_balance τ hcyclic _ _ _ _ Y
    (kmsModularWeight_intertwines_d hd hr u v)

theorem cyclic_support_balance_B (τ : A →ₗ[R] R)
    (hcyclic : ∀ x y : A, τ (x * y) = τ (y * x))
    {d B : A} (hB : B * B = 0) (hs : B * d * B = B) (u v : R) (Y : A) :
    (v * v) * τ (kmsModularWeight u v d B * (B * Y)) =
      (u * u) * τ (kmsModularWeight u v d B * (Y * B)) :=
  cyclic_weighted_balance τ hcyclic _ _ _ _ Y
    (kmsModularWeight_intertwines_B hB hs u v)

end InfoGeometry.Canonical.ReflexiveNilpotentFlows
