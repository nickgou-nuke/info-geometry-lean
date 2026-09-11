import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Statistical.DualFlatCurvature

/-!
# Curvature / standard-Zorn-derivation bridge

This is the stronger infinitesimal-holonomy lane.  It compares geometric
curvature operators with the repository-native standard derivations of the
alternative Zorn algebra.
-/

namespace InfoGeometry.Bridge

open InfoGeometry.Algebra

variable {T : Type*} [AddCommGroup T] [Module ℝ T]

/--
A two-map representation of curvature by standard split-octonion derivations.
The parameter map selects the derivation parameters; the carrier map realizes
geometric tangent vectors in the Zorn carrier.
-/
structure ZornCurvatureDerivationBridge
    (R0 : T → T → Module.End ℝ T) where
  parameterMap : T →ₗ[ℝ] ZornVectorMatrix ℝ
  carrierMap : T →ₗ[ℝ] ZornVectorMatrix ℝ
  carrier_injective : Function.Injective carrierMap

  scale : ℝ
  scale_ne_zero : scale ≠ 0

  curvature_intertwining : ∀ X Y,
    carrierMap.comp (R0 X Y) =
      scale •
        (zornStanDerivation (parameterMap X) (parameterMap Y)).toLinearMap.comp carrierMap

namespace ZornCurvatureDerivationBridge

variable {R0 : T → T → Module.End ℝ T}

/-- Pointwise curvature/derivation intertwining. -/
theorem curvature_intertwining_apply
    (B : ZornCurvatureDerivationBridge (T := T) R0)
    (X Y Z : T) :
    B.carrierMap (R0 X Y Z) =
      B.scale • zornStanDerivation (B.parameterMap X) (B.parameterMap Y) (B.carrierMap Z) := by
  have h := LinearMap.congr_fun (B.curvature_intertwining X Y) Z
  simpa using h

/--
Normal-form readout of the curvature representation through the canonical Zorn
standard derivation.
-/
theorem curvature_intertwining_normal_form
    (B : ZornCurvatureDerivationBridge (T := T) R0)
    (X Y Z : T) :
    B.carrierMap (R0 X Y Z) =
      B.scale •
        ((((B.parameterMap X * B.parameterMap Y) -
              (B.parameterMap Y * B.parameterMap X)) * B.carrierMap Z -
            B.carrierMap Z *
              ((B.parameterMap X * B.parameterMap Y) -
                (B.parameterMap Y * B.parameterMap X))) -
          3 • associator (B.parameterMap X) (B.parameterMap Y) (B.carrierMap Z)) := by
  rw [B.curvature_intertwining_apply X Y Z]
  rw [zornStanDerivation_apply_normal_form]

end ZornCurvatureDerivationBridge

end InfoGeometry.Bridge
