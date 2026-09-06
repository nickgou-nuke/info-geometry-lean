import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Geometry.Statistical.DualFlatCurvature

/-!
# Amari--Zorn standard-derivation bridge

The standard alternative derivation

`D_{a,b} = [L_a,L_b] + [L_a,R_b] + [R_a,R_b]`

is an honest infinitesimal algebra automorphism.  This module packages the
stronger, derivation-valued version of the curvature intertwining problem.
-/

namespace InfoGeometry.Bridge

open InfoGeometry.Algebra

variable {T A : Type*}
variable [AddCommGroup T] [Module ℝ T]
variable [NonUnitalNonAssocRing A] [Module ℝ A]
variable [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

/--
A curvature representation through the standard derivations of an alternative
algebra.  The alternative laws are explicit hypotheses rather than hidden
axioms.
-/
structure AmariZornDerivationBridge
    (Rzero : T → T → Module.End ℝ T)
    (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hright : ∀ x y : A, (y * x) * x = y * (x * x)) where
  parameterMap : T →ₗ[ℝ] A
  carrierMap : T →ₗ[ℝ] A
  scale : ℝ
  scale_ne_zero : scale ≠ 0
  curvature_intertwining :
    ∀ X Y,
      carrierMap.comp (Rzero X Y) =
        scale •
          ((stanDerivation
            (R := ℝ) hleft hright (parameterMap X) (parameterMap Y)).toLinearMap.comp
              carrierMap)

namespace AmariZornDerivationBridge

variable {Rzero : T → T → Module.End ℝ T}
variable {hleft : ∀ x y : A, (x * x) * y = x * (x * y)}
variable {hright : ∀ x y : A, (y * x) * x = y * (x * x)}
variable
  (B : AmariZornDerivationBridge
    (T := T) (A := A) Rzero hleft hright)

/-- Pointwise form of the derivation-valued curvature intertwiner. -/
theorem curvature_intertwining_apply
    (X Y Z : T) :
    B.carrierMap (Rzero X Y Z) =
      B.scale •
        stanDerivation
          (R := ℝ) hleft hright (B.parameterMap X) (B.parameterMap Y)
          (B.carrierMap Z) := by
  have h := congrArg
    (fun F : T →ₗ[ℝ] A => F Z)
    (B.curvature_intertwining X Y)
  simpa using h

/-- The standard derivation used by the bridge satisfies the Leibniz rule. -/
theorem bridge_derivation_leibniz
    (X Y : T) (u v : A) :
    stanDerivation
        (R := ℝ) hleft hright (B.parameterMap X) (B.parameterMap Y) (u * v) =
      stanDerivation
          (R := ℝ) hleft hright (B.parameterMap X) (B.parameterMap Y) u * v +
        u * stanDerivation
          (R := ℝ) hleft hright (B.parameterMap X) (B.parameterMap Y) v := by
  exact NonAssocDerivation.leibniz
    (stanDerivation
      (R := ℝ) hleft hright (B.parameterMap X) (B.parameterMap Y)) u v

/-- Kleinfeld normal form for the derivation acting on a represented tangent vector. -/
theorem bridge_derivation_normal_form
    (X Y Z : T) :
    stanDerivation
        (R := ℝ) hleft hright (B.parameterMap X) (B.parameterMap Y)
        (B.carrierMap Z) =
      (((B.parameterMap X * B.parameterMap Y) -
          (B.parameterMap Y * B.parameterMap X)) * B.carrierMap Z -
        B.carrierMap Z *
          ((B.parameterMap X * B.parameterMap Y) -
            (B.parameterMap Y * B.parameterMap X))) -
        3 • associator (B.parameterMap X) (B.parameterMap Y) (B.carrierMap Z) := by
  change stanDerMap
      (R := ℝ) (B.parameterMap X) (B.parameterMap Y) (B.carrierMap Z) = _
  exact stanDerMap_apply_normal_form
    (R := ℝ) hleft hright (B.parameterMap X) (B.parameterMap Y) (B.carrierMap Z)

end AmariZornDerivationBridge

end InfoGeometry.Bridge
