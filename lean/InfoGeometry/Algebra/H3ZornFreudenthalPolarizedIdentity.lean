import InfoGeometry.Algebra.H3ZornFreudenthalQuadraticLaws
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.FreudenthalSymplecticAction

/-!
# Polarized Freudenthal identity on the native split-Albert carrier

This owner exposes the first genuine Albert-specific edge needed before an
`aut(F,ω,q)` construction: the polarized adjoint identity.  It reuses the
existing H₃(Zorn) quadratic-law package and introduces no new charge carrier
or exceptional-group assumption.
-/

namespace InfoGeometry.Algebra.H3ZornFreudenthal

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Exceptional.Freudenthal

theorem h3zorn_adjoint_cross_linearization
    (X Y : H3Zorn ℝ) :
    H3Zorn.crossProduct (H3Zorn.adjointQuad X)
        (H3Zorn.crossProduct X Y) =
      H3Zorn.normCubic X • Y +
        H3Zorn.traceBilin (H3Zorn.adjointQuad X) Y • X := by
  exact CubicJordanQuadraticLaws.adjoint_cross_linearization
    h3zornCubicJordanQuadraticLaws X Y

theorem h3zorn_adjoint_cross_linearization_swap
    (X Y : H3Zorn ℝ) :
    H3Zorn.crossProduct (H3Zorn.adjointQuad Y)
        (H3Zorn.crossProduct Y X) =
      H3Zorn.normCubic Y • X +
        H3Zorn.traceBilin (H3Zorn.adjointQuad Y) X • Y := by
  exact CubicJordanQuadraticLaws.adjoint_cross_linearization
    h3zornCubicJordanQuadraticLaws Y X

theorem h3zorn_freudenthal_triple_commutator
    (X Y U V : FreudenthalCharge (H3Zorn ℝ)) :
    ⁅symplecticRankTwo h3zornCubicJordanDatum X Y,
        symplecticRankTwo h3zornCubicJordanDatum U V⁆ =
      symplecticRankTwo h3zornCubicJordanDatum
        (symplecticRankTwo h3zornCubicJordanDatum X Y U) V +
        symplecticRankTwo h3zornCubicJordanDatum U
          (symplecticRankTwo h3zornCubicJordanDatum X Y V) := by
  exact symplectic_rankTwo_commutator_rankTwo
    h3zornCubicJordanDatum X Y U V

end InfoGeometry.Algebra.H3ZornFreudenthal
