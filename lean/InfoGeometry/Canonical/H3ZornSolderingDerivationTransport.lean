import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.H3ZornAlgebraicSoldering

noncomputable section

namespace InfoGeometry.Canonical.H3ZornSolderingDerivationTransport

open InfoGeometry.Algebra
open InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding
open InfoGeometry.Canonical.H3ZornAlgebraicSoldering

/-- Direct form of transport of a Leibniz derivation through an algebraic
soldering equivalence.  This is the unbundled theorem corresponding to
`AlgebraicSoldering.derivation_transport`. -/
theorem jordanDerivation_transport
    {A J : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup J] [Module ℝ J]
    (coordMul : A → A → A) (jordanMul : J → J → J)
    (S : A ≃ₗ[ℝ] J)
    (hS : ∀ x y, S (coordMul x y) = jordanMul (S x) (S y))
    (D : Module.End ℝ A)
    (hD : ∀ x y, D (coordMul x y) =
      coordMul (D x) y + coordMul x (D y)) :
    let Dhat := S.toLinearMap.comp (D.comp S.symm.toLinearMap)
    ∀ x y : J,
      Dhat (jordanMul x y) =
        jordanMul (Dhat x) y + jordanMul x (Dhat y) := by
  let AS : AlgebraicSoldering A J :=
    { equiv := S
      coordMul := coordMul
      targetMul := jordanMul
      map_mul := hS }
  intro Dhat x y
  change AS.transportEnd D (AS.targetMul x y) =
    AS.targetMul (AS.transportEnd D x) y +
      AS.targetMul x (AS.transportEnd D y)
  exact AS.derivation_transport D hD x y

/-- The concrete commutative square for PR #135: the native entrywise H3
operator is exactly the transport of its Peirce-coordinate pullback through
`h3Soldering`. -/
theorem liftG2End_is_transported (D : G2Derivation) :
    liftG2End D =
      h3Soldering.toLinearMap.comp
        ((coordLiftG2 D).comp h3Soldering.symm.toLinearMap) := by
  symm
  exact transport_coordLiftG2_eq_liftG2End D

/-- Direct specialization of the generic soldering theorem to the H3 Peirce
chart.  Any independently established coordinate Leibniz theorem immediately
produces the native H3 Jordan-derivation law. -/
theorem liftG2End_isJordanDerivation_of_coordinate
    (D : G2Derivation) (hD : CoordinateJordanLeibniz D) :
    H3ZornJordanDerivation (liftG2End D) := by
  exact entrywiseJordanCompatible_of_coordinateLeibniz D hD

/-- Final closure theorem once the single coordinate-side Leibniz theorem is
available uniformly.  No ambient 27-coordinate calculation is required. -/
theorem full_g2_f4_compatibility_of_coordinate
    (hcoord : ∀ D : G2Derivation, CoordinateJordanLeibniz D) :
    FullEntrywiseG2F4Compatibility := by
  exact fullEntrywiseCompatibility_iff_coordinateLeibniz.mpr hcoord

/-- The full entrywise G2-to-F4 compatibility is therefore exactly equivalent
to the uniform coordinate Leibniz theorem. -/
theorem full_g2_f4_compatibility_iff_coordinate :
    FullEntrywiseG2F4Compatibility ↔
      ∀ D : G2Derivation, CoordinateJordanLeibniz D :=
  fullEntrywiseCompatibility_iff_coordinateLeibniz

end InfoGeometry.Canonical.H3ZornSolderingDerivationTransport

