import InfoGeometry.Algebra.Zorn.G2CASPointOrbit

/-!
# Transitivity of the native isotropic-point action

The explicit point-orbit words already cover the 63-point native carrier.
This owner exposes that fact at the subtype action level needed by the
uniform line-fibre argument.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativePointTransitivity

open InfoGeometry.Algebra.Zorn.G2CASPointOrbit
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem octImPointPerm_base_surjective :
    Function.Surjective
      (fun g : SplitOctF2Aut =>
        octImPointPerm g nativeBaseIsotropicPoint) := by
  intro v
  obtain ⟨w, hw⟩ := native_point_orbit_cover v
  refine ⟨pointWordProd w, ?_⟩
  apply Subtype.ext
  change octImAction (pointWordProd w) nativeBasePoint = v.1
  exact hw

end InfoGeometry.Algebra.Zorn.G2NativePointTransitivity
