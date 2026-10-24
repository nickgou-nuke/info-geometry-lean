/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.NCG.NoncommutativeCyclicCocycle
import InfoGeometry.OperatorAlgebra.CARProjectors

/-! # Tracial CAR densities -- uncompiled sandbox candidate

Only linearity, cyclicity, native units and native CAR are used. These are
algebraic weighted functionals, not positive normalized GNS states.
-/
namespace InfoGeometry.Sandbox.TracialCARDensity20261024

open InfoGeometry.NCG
open InfoGeometry.OperatorAlgebra.CARProjectors
open SplitClifford

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Left density weighting of the existing tracial linear functional. -/
def weighted (τ : TracialFunctional R A) (ρ : A) : A →ₗ[R] R :=
  τ.toLinearMap.comp (LinearMap.mulLeft R ρ)

@[simp] theorem weighted_apply (τ : TracialFunctional R A) (ρ x : A) :
    weighted τ ρ x = τ (ρ * x) := rfl

/-- Transporting the density pulls the observable back by the inverse unit. -/
theorem inverse_pullback (τ : TracialFunctional R A) (u : Aˣ) (ρ x : A) :
    weighted τ ((u : A) * ρ * (↑(u⁻¹) : A)) x =
      weighted τ ρ ((↑(u⁻¹) : A) * x * (u : A)) := by
  change τ (((u : A) * ρ * (↑(u⁻¹) : A)) * x) =
    τ (ρ * ((↑(u⁻¹) : A) * x * (u : A)))
  calc
    _ = τ ((u : A) * (ρ * ((↑(u⁻¹) : A) * x))) := by simp only [mul_assoc]
    _ = τ ((ρ * ((↑(u⁻¹) : A) * x)) * (u : A)) := τ.cyclic _ _
    _ = _ := by simp only [mul_assoc]

/-- Joint transport preserves the weighted readout, without any star premise. -/
theorem joint_covariance (τ : TracialFunctional R A) (u : Aˣ) (ρ x : A) :
    weighted τ ((u : A) * ρ * (↑(u⁻¹) : A))
      ((u : A) * x * (↑(u⁻¹) : A)) = weighted τ ρ x := by
  rw [inverse_pullback]
  congr 1
  simp [mul_assoc]

/-- General division-free boundary identity. The law ηρ = k suffices. -/
theorem divisionFreeKMS (τ : TracialFunctional R A) (ρ η x y : A) (k : R)
    (hηρ : η * ρ = k • (1 : A)) :
    k * weighted τ ρ (x * y) = weighted τ ρ (y * (ρ * x * η)) := by
  symm
  change τ (ρ * (y * (ρ * x * η))) = k * τ (ρ * (x * y))
  calc
    _ = τ ((y * (ρ * x * η)) * ρ) := τ.cyclic _ _
    _ = τ ((y * (ρ * x)) * (η * ρ)) := by simp only [mul_assoc]
    _ = τ (k • (y * (ρ * x))) := by rw [hηρ, mul_smul_comm, mul_one]
    _ = k * τ (y * (ρ * x)) := by rw [τ.map_smul]; rfl
    _ = k * τ ((ρ * x) * y) := by rw [τ.cyclic y (ρ * x)]
    _ = _ := by rw [mul_assoc]

/-- Native CAR normalization supplies reflexive absorption, not an extra field. -/
theorem ann_cre_ann (P : CARPair A) : P.ann * (P.cre * P.ann) = P.ann := by
  have h : P.ann * P.cre = 1 - P.cre * P.ann := eq_sub_of_add_eq P.anti
  rw [← mul_assoc, h, sub_mul, one_mul, mul_assoc, P.ann_sq, mul_zero, sub_zero]

theorem cre_ann_cre (P : CARPair A) : P.cre * (P.ann * P.cre) = P.cre := by
  exact ann_cre_ann (particleHole P)

/-- Occupation weight a multiplies Bb; vacuum weight c multiplies bB. -/
def density (P : CARPair A) (a c : R) : A := a • minus P + c • plus P

/-- Algebraic adjugate: the two complementary weights are exchanged. -/
def densityAdjugate (P : CARPair A) (a c : R) : A := c • minus P + a • plus P

theorem density_mul_ann (P : CARPair A) (a c : R) :
    density P a c * P.ann = c • P.ann := by
  simp only [density, minus, plus, add_mul, smul_mul_assoc, mul_assoc,
    P.ann_sq, mul_zero, smul_zero, zero_add, ann_cre_ann]

theorem ann_mul_density (P : CARPair A) (a c : R) :
    P.ann * density P a c = a • P.ann := by
  change P.ann * (a • (P.cre * P.ann) + c • (P.ann * P.cre)) = _
  rw [mul_add, mul_smul_comm, mul_smul_comm, ann_cre_ann,
    ← mul_assoc, P.ann_sq, zero_mul, smul_zero, add_zero]

theorem density_mul_cre (P : CARPair A) (a c : R) :
    density P a c * P.cre = a • P.cre := by
  simp only [density, minus, plus, add_mul, smul_mul_assoc, mul_assoc,
    P.cre_sq, mul_zero, smul_zero, add_zero, cre_ann_cre]

theorem cre_mul_density (P : CARPair A) (a c : R) :
    P.cre * density P a c = c • P.cre := by
  change P.cre * (a • (P.cre * P.ann) + c • (P.ann * P.cre)) = _
  rw [mul_add, mul_smul_comm, mul_smul_comm, cre_ann_cre,
    ← mul_assoc, P.cre_sq, zero_mul, smul_zero, zero_add]

/-- Product law in the existing two complementary CAR sectors. -/
theorem density_mul_density (P : CARPair A) (a c d e : R) :
    density P a c * density P d e = density P (a * d) (c * e) := by
  simp only [density, add_mul, mul_add, smul_mul_smul, minus_idempotent,
    plus_idempotent, minus_mul_plus, plus_mul_minus, smul_zero, add_zero, zero_add]

theorem density_mul_adjugate (P : CARPair A) (a c : R) :
    density P a c * densityAdjugate P a c = (a * c) • (1 : A) := by
  change density P a c * density P c a = _
  rw [density_mul_density]
  simp only [density, mul_comm c a, ← smul_add]
  rw [add_comm (minus P), projectors_add]

theorem adjugate_mul_density (P : CARPair A) (a c : R) :
    densityAdjugate P a c * density P a c = (a * c) • (1 : A) := by
  change density P c a * density P a c = _
  rw [density_mul_density]
  simp only [density, mul_comm c a, ← smul_add]
  rw [add_comm (minus P), projectors_add]

theorem density_divisionFreeKMS (τ : TracialFunctional R A) (P : CARPair A)
    (a c : R) (x y : A) :
    (a * c) * weighted τ (density P a c) (x * y) =
      weighted τ (density P a c) (y * (density P a c * x * densityAdjugate P a c)) :=
  divisionFreeKMS τ _ _ x y (a * c) (adjugate_mul_density P a c)

/-- Generic scalar eigenproduct boundary rule; no ratios or inverses. -/
theorem eigenproductKMS (τ : TracialFunctional R A) (ρ z x : A) (l r : R)
    (hl : ρ * z = l • z) (hr : z * ρ = r • z) :
    r * weighted τ ρ (z * x) = l * weighted τ ρ (x * z) := by
  have hz : weighted τ ρ (z * x) = l * τ (z * x) := by
    rw [weighted_apply, ← mul_assoc, hl, smul_mul_assoc, τ.map_smul]; rfl
  have hx : weighted τ ρ (x * z) = r * τ (z * x) := by
    rw [weighted_apply, ← mul_assoc, τ.cyclic (ρ * x) z, ← mul_assoc,
      hr, smul_mul_assoc, τ.map_smul]; rfl
  rw [hz, hx]
  ring

theorem annihilatorKMS (τ : TracialFunctional R A) (P : CARPair A) (a c : R) (x : A) :
    a * weighted τ (density P a c) (P.ann * x) =
      c * weighted τ (density P a c) (x * P.ann) :=
  eigenproductKMS τ _ _ x c a (density_mul_ann P a c) (ann_mul_density P a c)

theorem creatorKMS (τ : TracialFunctional R A) (P : CARPair A) (a c : R) (x : A) :
    c * weighted τ (density P a c) (P.cre * x) =
      a * weighted τ (density P a c) (x * P.cre) :=
  eigenproductKMS τ _ _ x a c (density_mul_cre P a c) (cre_mul_density P a c)

theorem occupation_readout (τ : TracialFunctional R A) (P : CARPair A) (a c : R) :
    weighted τ (density P a c) (minus P) = a * τ (minus P) := by
  simp only [weighted_apply, density, add_mul, smul_mul_assoc,
    minus_idempotent, plus_mul_minus, smul_zero, add_zero, τ.map_smul]
  rfl

theorem vacuum_readout (τ : TracialFunctional R A) (P : CARPair A) (a c : R) :
    weighted τ (density P a c) (plus P) = c * τ (plus P) := by
  simp only [weighted_apply, density, add_mul, smul_mul_assoc,
    plus_idempotent, minus_mul_plus, smul_zero, zero_add, τ.map_smul]
  rfl

/-- Correct commutator defect: vacuum minus occupation. -/
theorem density_defect (τ : TracialFunctional R A) (P : CARPair A) (a c : R) :
    weighted τ (density P a c) (P.ann * P.cre - P.cre * P.ann) =
      (c - a) * τ (plus P) := by
  change weighted τ (density P a c) (plus P - minus P) = _
  rw [map_sub, vacuum_readout, occupation_readout]
  have h : τ (minus P) = τ (plus P) := τ.cyclic P.cre P.ann
  rw [h]
  ring

/-- Vacuum density is bB, not Bb. No normalization of the trace is assumed. -/
theorem vacuum_density_defect (τ : TracialFunctional R A) (P : CARPair A) :
    weighted τ (plus P) (P.ann * P.cre - P.cre * P.ann) = τ (plus P) := by
  simpa only [density, zero_smul, one_smul, zero_add, sub_zero, one_mul] using
    density_defect τ P (0 : R) 1

/-- Tilted vacuum readout difference; no unconditional nonzero assertion. -/
theorem tilted_vacuum_difference (τ : TracialFunctional R A) (P : CARPair A)
    (u : Aˣ) (x : A) :
    weighted τ ((u : A) * plus P * (↑(u⁻¹) : A)) x - weighted τ (plus P) x =
      τ (plus P * ((↑(u⁻¹) : A) * x * (u : A) - x)) := by
  rw [inverse_pullback]
  simp only [weighted_apply, mul_sub, τ.map_sub]

/-- The actual vacuum support bB is killed on the left by b. -/
theorem ann_mul_vacuum (P : CARPair A) : P.ann * plus P = 0 := by
  change P.ann * (P.ann * P.cre) = 0
  rw [← mul_assoc, P.ann_sq, zero_mul]

/-- Operator excitation of the product vacuum; no nonzero claim or off-site
commutation is needed for this ordered identity. -/
theorem mixed_annihilator_vacuum (P₁ P₂ : CARPair A) (u v : R) :
    (u • P₁.ann + v • P₂.cre) * (plus P₁ * plus P₂) =
      v • (P₂.cre * (plus P₁ * plus P₂)) := by
  rw [add_mul, smul_mul_assoc, smul_mul_assoc,
    ← mul_assoc P₁.ann, ann_mul_vacuum, zero_mul, smul_zero, zero_add]

end InfoGeometry.Sandbox.TracialCARDensity20261024
