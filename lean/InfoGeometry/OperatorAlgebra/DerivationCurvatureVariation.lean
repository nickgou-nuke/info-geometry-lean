/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.Geometry.AssociativeGaugeConnection

/-! # Exact variations of native derivation-based curvature

All forms and differentials are the existing Chevalley--Eilenberg objects.
The quadratic remainder and the bracket of derivation directions are retained.
These are algebraic variation identities; analytic derivatives of finite
matrix connection energies are developed separately.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra
open LieModule.Cohomology

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

private theorem twoForm_ext {α β : TwoForm K}
    (h : ∀ x y, α x y = β x y) : α = β :=
  DFunLike.ext _ _ (fun x => LinearMap.ext (h x))

@[simp] private theorem twoForm_zero_apply (x y : K.L) :
    (0 : TwoForm K) x y = 0 := rfl

/-- Polarization of the actual commutator wedge square. -/
def connectionCrossWedge (Γ α : OneForm K) : TwoForm K :=
  connectionWedgeSquare K (Γ + α) - connectionWedgeSquare K Γ -
    connectionWedgeSquare K α

@[simp] theorem connectionCrossWedge_apply (Γ α : OneForm K) (x y : K.L) :
    connectionCrossWedge K Γ α x y =
      Γ x * α y - α y * Γ x - Γ y * α x + α x * Γ y := by
  change connectionWedgeSquare K (Γ + α) x y - connectionWedgeSquare K Γ x y -
    connectionWedgeSquare K α x y = _
  simp only [connectionWedgeSquare_apply, LinearMap.add_apply]
  noncomm_ring

theorem connectionCrossWedge_comm (Γ α : OneForm K) :
    connectionCrossWedge K Γ α = connectionCrossWedge K α Γ := by
  apply twoForm_ext K
  intro x y
  simp only [connectionCrossWedge_apply]
  noncomm_ring

/-- The native linearized curvature map `d_Γ` on one-cochains. -/
def curvatureLinearization (Γ : OneForm K) : OneForm K →ₗ[R] TwoForm K where
  toFun α := exteriorDerivativeOne K α + connectionCrossWedge K Γ α
  map_add' α β := by
    apply twoForm_ext K
    intro x y
    simp only [map_add, add_apply_apply, LinearMap.add_apply, exteriorDerivativeOne_apply,
      connectionCrossWedge_apply]
    noncomm_ring
  map_smul' r α := by
    apply twoForm_ext K
    intro x y
    simp only [map_smul, add_apply_apply, smul_apply_apply, LinearMap.smul_apply,
      connectionCrossWedge_apply, smul_add, smul_sub, smul_mul_assoc,
      mul_smul_comm, RingHom.id_apply]

@[simp] theorem curvatureLinearization_apply (Γ α : OneForm K) (x y : K.L) :
    curvatureLinearization K Γ α x y =
      covariantDerivative K Γ x (α y) - covariantDerivative K Γ y (α x) -
        α ⁅x, y⁆ := by
  simp only [curvatureLinearization, LinearMap.coe_mk, AddHom.coe_mk,
    add_apply_apply, exteriorDerivativeOne_apply, connectionCrossWedge_apply,
    covariantDerivative]
  noncomm_ring

/-- Exact Taylor expansion in the algebraic connection space. -/
theorem connectionCurvature_add (Γ α : OneForm K) :
    connectionCurvature K (Γ + α) = connectionCurvature K Γ +
      curvatureLinearization K Γ α + connectionWedgeSquare K α := by
  apply twoForm_ext K
  intro x y
  simp only [add_apply_apply, connectionCurvature_apply, curvatureLinearization_apply,
    connectionWedgeSquare_apply, LinearMap.add_apply, map_add, covariantDerivative]
  noncomm_ring

theorem connectionWedgeSquare_smul (α : OneForm K) (t : R) :
    connectionWedgeSquare K (t • α) = t ^ 2 • connectionWedgeSquare K α := by
  apply twoForm_ext K
  intro x y
  simp only [smul_apply_apply, connectionWedgeSquare_apply, LinearMap.smul_apply,
    smul_mul_assoc, mul_smul_comm, smul_smul, ← smul_sub, pow_two]

/-- The quadratic term is the full noncommutative self-wedge. -/
theorem connectionCurvature_add_smul (Γ α : OneForm K) (t : R) :
    connectionCurvature K (Γ + t • α) = connectionCurvature K Γ +
      t • curvatureLinearization K Γ α + t ^ 2 • connectionWedgeSquare K α := by
  rw [connectionCurvature_add, map_smul, connectionWedgeSquare_smul]

/-- The mixed second difference is independent of the background connection. -/
theorem connectionCurvature_mixed_difference (Γ α β : OneForm K) :
    connectionCurvature K (Γ + α + β) - connectionCurvature K (Γ + α) -
      connectionCurvature K (Γ + β) + connectionCurvature K Γ =
        connectionCrossWedge K α β := by
  apply twoForm_ext K
  intro x y
  change connectionCurvature K (Γ + α + β) x y - connectionCurvature K (Γ + α) x y -
    connectionCurvature K (Γ + β) x y + connectionCurvature K Γ x y = _
  simp only [connectionCurvature_apply,
    connectionCrossWedge_apply, LinearMap.add_apply, map_add]
  noncomm_ring

/-- The induced covariant differential of an algebra-valued zero-form. -/
def covariantExteriorDerivativeZero (Γ : OneForm K) (a : A) : OneForm K :=
  exteriorDerivativeZero K a + (LinearMap.mulRight R a).comp Γ -
    (LinearMap.mulLeft R a).comp Γ

@[simp] theorem covariantExteriorDerivativeZero_apply
    (Γ : OneForm K) (a : A) (x : K.L) :
    covariantExteriorDerivativeZero K Γ a x = covariantDerivative K Γ x a := rfl

/-- Infinitesimal gauge directions act on curvature by its inner derivation. -/
theorem curvatureLinearization_covariantExteriorDerivativeZero
    (Γ : OneForm K) (a : A) (x y : K.L) :
    curvatureLinearization K Γ (covariantExteriorDerivativeZero K Γ a) x y =
      connectionCurvature K Γ x y * a - a * connectionCurvature K Γ x y := by
  simpa only [curvatureLinearization_apply, covariantExteriorDerivativeZero_apply]
    using covariantDerivative_commutator K Γ x y a

/-- Flat connections have infinitesimal gauge directions in the linearized kernel. -/
theorem curvatureLinearization_gauge_eq_zero_of_flat
    (Γ : OneForm K) (hΓ : connectionCurvature K Γ = 0) (a : A) :
    curvatureLinearization K Γ (covariantExteriorDerivativeZero K Γ a) = 0 := by
  apply twoForm_ext K
  intro x y
  rw [curvatureLinearization_covariantExteriorDerivativeZero, hΓ]
  simp

/-- Explicit comparison with the existing regular-module curvature convention.
The Lie-direction correction is retained unless its vanishing is proved. -/
theorem connectionCurvature_eq_regular_curvature_sub
    (Γ : OneForm K) (x y : K.L) :
    connectionCurvature K Γ x y =
      InfoGeometry.Geometry.AssociativeGaugeConnection.curvature
        (K.operatorAction x) (K.operatorAction y) (Γ x) (Γ y) - Γ ⁅x, y⁆ := by
  simp only [connectionCurvature_apply,
    InfoGeometry.Geometry.AssociativeGaugeConnection.curvature]
  noncomm_ring

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
