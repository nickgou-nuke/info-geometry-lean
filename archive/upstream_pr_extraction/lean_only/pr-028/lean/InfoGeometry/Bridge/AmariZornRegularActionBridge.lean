import Mathlib.LinearAlgebra.BilinearForm.Basic
import InfoGeometry.Algebra.Zorn.RegularActionAssociator
import InfoGeometry.Geometry.Statistical.DualFlatCurvature

/-!
# Amari--Zorn regular-action curvature bridge

This module packages the nontrivial data required to compare a geometric
curvature operator with the Zorn left/right regular-action obstruction.
Parameter and carrier maps are deliberately distinct.  The Zorn operator is
restricted to an explicit invariant carrier `W`; no ad-hoc projection is used.
-/

namespace InfoGeometry.Bridge

open InfoGeometry.Algebra
open InfoGeometry.Geometry.Statistical

variable {T A W : Type*}
variable [AddCommGroup T] [Module ℝ T]
variable [NonUnitalNonAssocRing A] [Module ℝ A]
variable [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
variable [AddCommGroup W] [Module ℝ W]

/--
A theorem-safe two-map bridge from a geometric curvature family to restricted
Zorn regular-action commutators.
-/
structure AmariZornRegularActionBridge
    (Rzero : T → T → Module.End ℝ T) where
  /-- Parameters selecting the left/right Zorn regular actions. -/
  parameterMap : T →ₗ[ℝ] A
  /-- Carrier realization of geometric tangent vectors. -/
  carrierMap : T →ₗ[ℝ] W
  /-- Inclusion of the invariant carrier into the ambient nonassociative algebra. -/
  inclusion : W →ₗ[ℝ] A
  inclusion_injective : Function.Injective inclusion
  /-- The actual restricted left/right obstruction on the invariant carrier. -/
  restrictedLR : T → T → Module.End ℝ W
  /-- Restriction certificate: the bundled operator is the ambient Zorn operator on `W`. -/
  restrictedLR_spec :
    ∀ X Y,
      inclusion.comp (restrictedLR X Y) =
        (leftRightCommutator
          (R := ℝ) (parameterMap X) (parameterMap Y)).comp inclusion
  /-- Bilinear metric on the invariant carrier. -/
  metric : LinearMap.BilinForm ℝ W
  metric_symm : ∀ u v, metric u v = metric v u
  metric_nondegenerate : ∀ u, (∀ v, metric u v = 0) → u = 0
  /-- The restricted Zorn obstruction is skew-adjoint for the carrier metric. -/
  restrictedLR_skew :
    ∀ X Y u v,
      metric (restrictedLR X Y u) v +
        metric u (restrictedLR X Y v) = 0
  /-- Nonzero relative curvature scale. -/
  scale : ℝ
  scale_ne_zero : scale ≠ 0
  /-- Master operator intertwining equation on the invariant carrier. -/
  curvature_intertwining :
    ∀ X Y,
      carrierMap.comp (Rzero X Y) =
        scale • ((restrictedLR X Y).comp carrierMap)

namespace AmariZornRegularActionBridge

variable {Rzero : T → T → Module.End ℝ T}
variable (B : AmariZornRegularActionBridge (T := T) (A := A) (W := W) Rzero)

/-- Pointwise form of the invariant-subspace restriction certificate. -/
theorem restrictedLR_spec_apply
    (X Y : T) (w : W) :
    B.inclusion (B.restrictedLR X Y w) =
      leftRightCommutator
        (R := ℝ) (B.parameterMap X) (B.parameterMap Y) (B.inclusion w) := by
  have h := congrArg
    (fun F : W →ₗ[ℝ] A => F w)
    (B.restrictedLR_spec X Y)
  simpa using h

/-- The ambient regular-action obstruction preserves the explicitly included carrier. -/
theorem ambient_leftRight_preserves_carrier
    (X Y : T) (w : W) :
    leftRightCommutator
        (R := ℝ) (B.parameterMap X) (B.parameterMap Y) (B.inclusion w) =
      B.inclusion (B.restrictedLR X Y w) := by
  exact (B.restrictedLR_spec_apply X Y w).symm

/-- Pointwise form of the curvature/operator intertwining relation. -/
theorem curvature_intertwining_apply
    (X Y Z : T) :
    B.carrierMap (Rzero X Y Z) =
      B.scale • B.restrictedLR X Y (B.carrierMap Z) := by
  have h := congrArg
    (fun F : T →ₗ[ℝ] W => F Z)
    (B.curvature_intertwining X Y)
  simpa using h

/-- The two-map soldering equation expressed in the ambient Zorn carrier. -/
theorem curvature_intertwining_ambient
    (X Y Z : T) :
    B.inclusion (B.carrierMap (Rzero X Y Z)) =
      B.scale •
        leftRightCommutator
          (R := ℝ) (B.parameterMap X) (B.parameterMap Y)
          (B.inclusion (B.carrierMap Z)) := by
  calc
    B.inclusion (B.carrierMap (Rzero X Y Z)) =
        B.inclusion
          (B.scale • B.restrictedLR X Y (B.carrierMap Z)) := by
      rw [B.curvature_intertwining_apply X Y Z]
    _ = B.scale • B.inclusion (B.restrictedLR X Y (B.carrierMap Z)) := by
      rw [map_smul]
    _ = B.scale •
        leftRightCommutator
          (R := ℝ) (B.parameterMap X) (B.parameterMap Y)
          (B.inclusion (B.carrierMap Z)) := by
      rw [B.restrictedLR_spec_apply X Y (B.carrierMap Z)]

/--
First Bianchi identity transports to a genuine compatibility identity for the
restricted Zorn obstruction.  The two-map architecture makes this nontrivial:
the third input is the carrier image, not another copy of the parameter map.
-/
theorem restrictedLR_bianchi
    (hBianchi :
      ∀ X Y Z : T,
        Rzero X Y Z + Rzero Y Z X + Rzero Z X Y = 0)
    (X Y Z : T) :
    B.restrictedLR X Y (B.carrierMap Z) +
        B.restrictedLR Y Z (B.carrierMap X) +
        B.restrictedLR Z X (B.carrierMap Y) = 0 := by
  have hgeom := congrArg B.carrierMap (hBianchi X Y Z)
  simp only [map_add, map_zero] at hgeom
  rw [B.curvature_intertwining_apply X Y Z,
    B.curvature_intertwining_apply Y Z X,
    B.curvature_intertwining_apply Z X Y] at hgeom
  have hscaled :
      B.scale •
        (B.restrictedLR X Y (B.carrierMap Z) +
          B.restrictedLR Y Z (B.carrierMap X) +
          B.restrictedLR Z X (B.carrierMap Y)) = 0 := by
    simpa [smul_add, add_assoc] using hgeom
  exact (smul_eq_zero.mp hscaled).resolve_left B.scale_ne_zero

/-- Skew-adjointness of the restricted obstruction, exposed as a theorem. -/
theorem restrictedLR_isSkew
    (X Y : T) (u v : W) :
    B.metric (B.restrictedLR X Y u) v +
      B.metric u (B.restrictedLR X Y v) = 0 :=
  B.restrictedLR_skew X Y u v

end AmariZornRegularActionBridge

end InfoGeometry.Bridge
