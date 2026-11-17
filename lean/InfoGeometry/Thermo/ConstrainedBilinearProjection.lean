/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Removing normalization and energy directions from a real bilinear form

For a real bilinear form, a vector `e` with `B e e = 1`, and an
energy direction `H`, first remove the `e` component and then the centered
energy component. The coefficients solve the two Gram normal equations.
The resulting native linear map projects onto the bilinear orthogonal
complement of `span {e, H}` and its kernel is exactly that constraint space.

Pulling back the form along this projection gives a positive semidefinite
form whenever the original form is positive semidefinite. Strict positivity
of the original form identifies the precise null space of the pullback.
The normalization coefficient is a Gram coefficient; no equality with a
Gibbs log-partition function is asserted away from equilibrium.
-/

noncomputable section

namespace InfoGeometry.Thermo.ConstrainedBilinearProjection

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Remove the component along the normalized direction `e`. -/
def center (B : LinearMap.BilinForm ℝ V) (e : V) : Module.End ℝ V :=
  LinearMap.id - (B e).smulRight e

@[simp] theorem center_apply (B : LinearMap.BilinForm ℝ V) (e x : V) :
    center B e x = x - B e x • e := rfl

/-- The energy coefficient obtained from the centered Gram equation. -/
def energyCoefficient (B : LinearMap.BilinForm ℝ V) (e H : V) : V →ₗ[ℝ] ℝ :=
  (B (center B e H) (center B e H))⁻¹ •
    ((B (center B e H)).comp (center B e))

@[simp] theorem energyCoefficient_apply
    (B : LinearMap.BilinForm ℝ V) (e H x : V) :
    energyCoefficient B e H x =
      B (center B e H) (center B e x) / B (center B e H) (center B e H) := by
  simp only [energyCoefficient, LinearMap.smul_apply, LinearMap.comp_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The normalization coefficient of the constrained Gram projection. -/
def identityCoefficient (B : LinearMap.BilinForm ℝ V) (e H : V) : V →ₗ[ℝ] ℝ :=
  B e - (B e H) • energyCoefficient B e H

@[simp] theorem identityCoefficient_apply
    (B : LinearMap.BilinForm ℝ V) (e H x : V) :
    identityCoefficient B e H x =
      B e x - energyCoefficient B e H x * B e H := by
  simp only [identityCoefficient, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, mul_comm]

/-- The actual linear projection removing both constraint directions. -/
def projection (B : LinearMap.BilinForm ℝ V) (e H : V) : Module.End ℝ V :=
  center B e - (energyCoefficient B e H).smulRight (center B e H)

theorem projection_apply (B : LinearMap.BilinForm ℝ V) (e H x : V) :
    projection B e H x =
      center B e x - energyCoefficient B e H x • center B e H := rfl

/-- The constraint space uses the native submodule span. -/
def constraintSubmodule (e H : V) : Submodule ℝ V :=
  Submodule.span ℝ ({e, H} : Set V)

/-- The explicit residual is `x - alpha(x) e - beta(x) H`. -/
theorem projection_eq_sub (B : LinearMap.BilinForm ℝ V) (e H x : V) :
    projection B e H x =
      x - identityCoefficient B e H x • e - energyCoefficient B e H x • H := by
  rw [projection_apply, identityCoefficient_apply]
  simp only [center_apply, smul_sub, sub_smul, smul_smul]
  module

theorem center_unit (B : LinearMap.BilinForm ℝ V) (e : V)
    (he : B e e = 1) : center B e e = 0 := by
  simp [he]

theorem center_pairing_left (B : LinearMap.BilinForm ℝ V) (e : V)
    (he : B e e = 1) (x : V) : B e (center B e x) = 0 := by
  simp [he]

theorem center_pairing_right (B : LinearMap.BilinForm ℝ V) (e : V)
    (hB : B.IsSymm) (he : B e e = 1) (x : V) :
    B (center B e x) e = 0 := by
  rw [hB.eq, center_pairing_left B e he]

theorem center_eq_zero_iff (B : LinearMap.BilinForm ℝ V) (e x : V)
    (he : B e e = 1) :
    center B e x = 0 ↔ x ∈ Submodule.span ℝ ({e} : Set V) := by
  constructor
  · intro hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨B e x, ?_⟩
    exact (sub_eq_zero.mp hx).symm
  · intro hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, center_unit B e he, smul_zero]

/-- Strict positivity supplies the denominator from the exact independence
condition: the energy is not a scalar multiple of the normalization vector. -/
theorem energy_denominator_pos (B : LinearMap.BilinForm ℝ V) (e H : V)
    (hpos : ∀ x : V, x ≠ 0 → 0 < B x x) (he : B e e = 1)
    (hH : H ∉ Submodule.span ℝ ({e} : Set V)) :
    0 < B (center B e H) (center B e H) := by
  apply hpos
  intro hz
  exact hH ((center_eq_zero_iff B e H he).mp hz)

theorem energyCoefficient_unit (B : LinearMap.BilinForm ℝ V) (e H : V)
    (he : B e e = 1) : energyCoefficient B e H e = 0 := by
  rw [energyCoefficient_apply, center_unit B e he]
  simp

theorem energyCoefficient_energy (B : LinearMap.BilinForm ℝ V) (e H : V)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    energyCoefficient B e H H = 1 := by
  rw [energyCoefficient_apply, div_self hden]

theorem projection_unit (B : LinearMap.BilinForm ℝ V) (e H : V)
    (he : B e e = 1) : projection B e H e = 0 := by
  rw [projection_apply, center_unit B e he, energyCoefficient_unit B e H he]
  simp

theorem projection_energy (B : LinearMap.BilinForm ℝ V) (e H : V)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    projection B e H H = 0 := by
  rw [projection_apply, energyCoefficient_energy B e H hden, one_smul, sub_self]

/-- First normal equation: the residual preserves the normalization constraint. -/
theorem projection_pairing_unit (B : LinearMap.BilinForm ℝ V) (e H : V)
    (he : B e e = 1) (x : V) : B e (projection B e H x) = 0 := by
  rw [projection_apply]
  simp only [map_sub, map_smul, center_pairing_left B e he]
  simp

theorem projection_pairing_centeredEnergy
    (B : LinearMap.BilinForm ℝ V) (e H : V)
    (hden : B (center B e H) (center B e H) ≠ 0) (x : V) :
    B (center B e H) (projection B e H x) = 0 := by
  rw [projection_apply, map_sub, map_smul, energyCoefficient_apply]
  simp only [smul_eq_mul]
  rw [div_mul_cancel₀ _ hden, sub_self]

/-- Second normal equation: the residual preserves the energy constraint. -/
theorem projection_pairing_energy (B : LinearMap.BilinForm ℝ V) (e H : V)
    (he : B e e = 1)
    (hden : B (center B e H) (center B e H) ≠ 0) (x : V) :
    B H (projection B e H x) = 0 := by
  have hc := projection_pairing_centeredEnergy B e H hden x
  have hu := projection_pairing_unit B e H he x
  simpa only [center_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, hu, smul_eq_mul, mul_zero, sub_zero] using hc

/-- The normal equations characterize the fixed vectors of the projection. -/
theorem projection_fixed (B : LinearMap.BilinForm ℝ V) (e H x : V)
    (heq : B e x = 0) (hHeq : B H x = 0) : projection B e H x = x := by
  have hc : center B e x = x := by simp [heq]
  have hCH : B (center B e H) x = 0 := by
    simp only [center_apply, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, hHeq, heq, smul_eq_mul, mul_zero, sub_zero]
  have hb : energyCoefficient B e H x = 0 := by
    rw [energyCoefficient_apply, hc, hCH, zero_div]
  rw [projection_apply, hc, hb, zero_smul, sub_zero]

theorem mem_orthogonal_constraints_iff
    (B : LinearMap.BilinForm ℝ V) (e H x : V) :
    x ∈ B.orthogonal (constraintSubmodule e H) ↔ B e x = 0 ∧ B H x = 0 := by
  simp [constraintSubmodule, LinearMap.BilinForm.orthogonal]

/-- A native projection onto the actual bilinear orthogonal complement. -/
theorem projection_isProj (B : LinearMap.BilinForm ℝ V) (e H : V)
    (he : B e e = 1)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    LinearMap.IsProj (B.orthogonal (constraintSubmodule e H)) (projection B e H) where
  map_mem x := (mem_orthogonal_constraints_iff B e H _).mpr
    ⟨projection_pairing_unit B e H he x,
      projection_pairing_energy B e H he hden x⟩
  map_id x hx := by
    obtain ⟨hu, henergy⟩ := (mem_orthogonal_constraints_iff B e H x).mp hx
    exact projection_fixed B e H x hu henergy

theorem projection_idempotent (B : LinearMap.BilinForm ℝ V) (e H : V)
    (he : B e e = 1)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    IsIdempotentElem (projection B e H) :=
  LinearMap.IsProj.isIdempotentElem (projection_isProj B e H he hden)

theorem projection_eq_zero_iff (B : LinearMap.BilinForm ℝ V) (e H x : V)
    (he : B e e = 1)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    projection B e H x = 0 ↔ x ∈ constraintSubmodule e H := by
  constructor
  · intro hx
    apply Submodule.mem_span_pair.mpr
    refine ⟨identityCoefficient B e H x, energyCoefficient B e H x, ?_⟩
    rw [projection_eq_sub] at hx
    have hx' := sub_eq_zero.mp hx
    calc
      identityCoefficient B e H x • e + energyCoefficient B e H x • H =
          energyCoefficient B e H x • H + identityCoefficient B e H x • e :=
        add_comm _ _
      _ = x := (sub_eq_iff_eq_add.mp hx').symm
  · intro hx
    obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [map_add, map_smul, map_smul,
      projection_unit B e H he, projection_energy B e H hden]
    simp

theorem projection_ker (B : LinearMap.BilinForm ℝ V) (e H : V)
    (he : B e e = 1)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    LinearMap.ker (projection B e H) = constraintSubmodule e H := by
  ext x
  exact projection_eq_zero_iff B e H x he hden

theorem projection_range (B : LinearMap.BilinForm ℝ V) (e H : V)
    (he : B e e = 1)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    LinearMap.range (projection B e H) = B.orthogonal (constraintSubmodule e H) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (projection_isProj B e H he hden).map_mem y
  · intro hx
    exact ⟨x, (projection_isProj B e H he hden).map_id x hx⟩

/-- The two spaces really are complementary, without an ambient dimension assumption. -/
theorem orthogonal_constraints_isCompl
    (B : LinearMap.BilinForm ℝ V) (e H : V)
    (he : B e e = 1)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    IsCompl (B.orthogonal (constraintSubmodule e H)) (constraintSubmodule e H) := by
  have hc := (projection_isProj B e H he hden).isCompl
  rw [projection_ker B e H he hden] at hc
  exact hc

/-- The constrained response as a native bilinear pullback. -/
def projectedForm (B : LinearMap.BilinForm ℝ V) (e H : V) :
    LinearMap.BilinForm ℝ V :=
  B.compl₁₂ (projection B e H) (projection B e H)

@[simp] theorem projectedForm_apply (B : LinearMap.BilinForm ℝ V) (e H x y : V) :
    projectedForm B e H x y = B (projection B e H x) (projection B e H y) := rfl

theorem projectedForm_isSymm (B : LinearMap.BilinForm ℝ V) (e H : V)
    (hB : B.IsSymm) : (projectedForm B e H).IsSymm :=
  ⟨fun x y => hB.eq _ _⟩

/-- The projected response equals evaluation on the actual projected vector. -/
theorem projectedForm_eq_pairing_right
    (B : LinearMap.BilinForm ℝ V) (e H x y : V)
    (he : B e e = 1)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    projectedForm B e H x y = B x (projection B e H y) := by
  rw [projectedForm_apply, projection_eq_sub B e H x]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    projection_pairing_unit B e H he y,
    projection_pairing_energy B e H he hden y,
    smul_zero, sub_zero]

/-- In the symmetric case this is a self-adjoint projection for the supplied form. -/
theorem projection_isSelfAdjoint (B : LinearMap.BilinForm ℝ V) (e H : V)
    (hB : B.IsSymm) (he : B e e = 1)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    B.IsSelfAdjoint (projection B e H) := by
  intro x y
  calc
    B (projection B e H x) y = B y (projection B e H x) := hB.eq _ _
    _ = projectedForm B e H y x :=
      (projectedForm_eq_pairing_right B e H y x he hden).symm
    _ = projectedForm B e H x y := (projectedForm_isSymm B e H hB).eq _ _
    _ = B x (projection B e H y) :=
      projectedForm_eq_pairing_right B e H x y he hden

theorem projectedForm_nonneg (B : LinearMap.BilinForm ℝ V) (e H : V)
    (hB : ∀ x : V, 0 ≤ B x x) (x : V) : 0 ≤ projectedForm B e H x x :=
  hB _

theorem projectedForm_isPosSemidef (B : LinearMap.BilinForm ℝ V) (e H : V)
    (hB : B.IsPosSemidef) : (projectedForm B e H).IsPosSemidef where
  isSymm := projectedForm_isSymm B e H hB.isSymm
  isNonneg := ⟨projectedForm_nonneg B e H hB.nonneg⟩

theorem projectedForm_unit (B : LinearMap.BilinForm ℝ V) (e H x : V)
    (he : B e e = 1) : projectedForm B e H e x = 0 := by
  rw [projectedForm_apply, projection_unit B e H he]
  simp

theorem projectedForm_energy (B : LinearMap.BilinForm ℝ V) (e H x : V)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    projectedForm B e H H x = 0 := by
  rw [projectedForm_apply, projection_energy B e H hden]
  simp

/-- The quadratic response has exactly the imposed constraints as its null space. -/
theorem projectedForm_self_eq_zero_iff
    (B : LinearMap.BilinForm ℝ V) (e H x : V)
    (hpos : ∀ y : V, y ≠ 0 → 0 < B y y) (he : B e e = 1)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    projectedForm B e H x x = 0 ↔ x ∈ constraintSubmodule e H := by
  rw [← projection_eq_zero_iff B e H x he hden]
  constructor
  · intro hz
    by_contra hn
    have hp := hpos (projection B e H x) hn
    change 0 < projectedForm B e H x x at hp
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · intro hz
    rw [projectedForm_apply, hz]
    simp

theorem projectedForm_self_pos_iff
    (B : LinearMap.BilinForm ℝ V) (e H x : V)
    (hpos : ∀ y : V, y ≠ 0 → 0 < B y y) (he : B e e = 1)
    (hden : B (center B e H) (center B e H) ≠ 0) :
    0 < projectedForm B e H x x ↔ x ∉ constraintSubmodule e H := by
  constructor
  · intro hp hx
    have hz := (projectedForm_self_eq_zero_iff B e H x hpos he hden).mpr hx
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · intro hx
    apply hpos
    intro hz
    exact hx ((projection_eq_zero_iff B e H x he hden).mp hz)

end InfoGeometry.Thermo.ConstrainedBilinearProjection
