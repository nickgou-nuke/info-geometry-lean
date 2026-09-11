import InfoGeometry.Algebra.H3ZornJordanIdentity
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.CubicJordanQuadraticLaws

/-!
# Reusable quadratic-law interface for the native split-Albert owner

This packages the existing `H3Zorn` polarization and adjoint laws.  It does
not introduce a second carrier or an exceptional Lie-algebra claim.
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
  map_add' := by
    intro X Y
    apply LinearMap.ext
    intro Z
    exact H3Zorn.crossProduct_add_left X Y Z
  map_smul' := by
    intro r X
    apply LinearMap.ext
    intro Y
    exact H3Zorn.crossProduct_smul_left r X Y

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
