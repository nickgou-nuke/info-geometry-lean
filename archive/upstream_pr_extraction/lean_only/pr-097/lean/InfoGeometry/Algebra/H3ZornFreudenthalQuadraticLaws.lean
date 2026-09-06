import InfoGeometry.Algebra.H3ZornJordanIdentity
import InfoGeometry.Exceptional.CubicJordanQuadraticLaws

/-!
# Quadratic-law interface for the canonical split Albert owner

This file exposes the already proved `H3Zorn` polarization and adjoint
identities through the reusable quadratic-law structure.  It introduces no
second Jordan or Freudenthal carrier.
-/

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Exceptional.Freudenthal

noncomputable def h3zornCrossLinear :
    H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ where
  toFun X :=
    { toFun := fun Y => crossProduct X Y
      map_add' := fun Y Z => H3Zorn.crossProduct_add_right X Y Z
      map_smul' := fun r Y => H3Zorn.crossProduct_smul_right r X Y }
  map_add' := fun X Y => by
    apply LinearMap.ext
    intro Z
    change crossProduct (X + Y) Z = crossProduct X Z + crossProduct Y Z
    exact H3Zorn.crossProduct_add_left X Y Z
  map_smul' := fun r X => by
    apply LinearMap.ext
    intro Y
    change crossProduct (r • X) Y = r • crossProduct X Y
    exact H3Zorn.crossProduct_smul_left r X Y

/-- The canonical quadratic-law package on the split Albert carrier. -/
noncomputable def h3zornCubicJordanQuadraticLaws :
    CubicJordanQuadraticLaws h3zornCubicJordanDatum where
  cross := h3zornCrossLinear
  cross_eq_polarization := by
    intro X Y
    rfl
  adjoint_smul := by
    intro a X
    exact H3Zorn.adjointQuad_smul a X
  norm_line := by
    intro r X Y
    exact H3Zorn.normCubic_line r X Y
  adjoint_adjoint := by
    intro X
    exact H3Zorn.adjointQuad_adjointQuad X

end InfoGeometry.Algebra
