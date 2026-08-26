import InfoGeometry.Algebra.Zorn.G2NativeWeylCartanRestriction
import InfoGeometry.Lie.CanonicalZornTransportedRootEigenrelation

/-!
# Root-space transport for a normalized native Weyl action

This owner supplies the carrier-correct specialization of the existing Cartan
normalizer lemma to the canonical root derivations.  The only remaining input
is the dual weight compatibility for the chosen target root; no sign or
normalization claim is made here.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceMembership

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceTransport
open InfoGeometry.Algebra.Zorn.G2NativeWeylCartanRestriction
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornMathlibRootSpace
open InfoGeometry.Lie.CanonicalZornTransportedRootEigenrelation

theorem conjugateCanonical_rootDerivation_mem_of_weight
    (i j : nonzeroIndex)
    (e : InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der ≃ₗ[ℝ]
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der)
    (c : axialCartanLieSubalgebra ≃ₗ[ℝ] axialCartanLieSubalgebra)
    (hbracket : ∀ X Y, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (hcartan : ∀ H : axialCartanLieSubalgebra,
      e (H : InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der) =
        ((c H : axialCartanLieSubalgebra) :
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der))
    (hweight : ∀ H : axialCartanLieSubalgebra,
      nativeRootWeight i (c.symm H) = nativeRootWeight j H) :
    e (rootDerivation i.1) ∈
      LieAlgebra.rootSpace axialCartanLieSubalgebra
        (nativeRootWeight j) := by
  apply InfoGeometry.Lie.CanonicalZornMathlibRootSpace.LinearEquiv.map_rootSpace_mem_of_cartan_normalizer
    i j e c hbracket hcartan hweight (rootDerivation i.1)
  intro H
  exact rootDerivation_bracket_eigen i H

theorem conjugateCanonical_rootDerivation_mem_of_weight_reflection
    (i j : nonzeroIndex)
    (e : InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der ≃ₗ[ℝ]
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der)
    (c : axialCartanLieSubalgebra ≃ₗ[ℝ] axialCartanLieSubalgebra)
    (hbracket : ∀ X Y, e ⁅X, Y⁆ = ⁅e X, e Y⁆)
    (hcartan : ∀ H : axialCartanLieSubalgebra,
      e (H : InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der) =
        ((c H : axialCartanLieSubalgebra) :
          InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.Der))
    (hweight : ∀ H : axialCartanLieSubalgebra,
      nativeRootWeight i (c.symm H) = nativeRootWeight j H) :
    e (rootDerivation i.1) ∈
      LieAlgebra.rootSpace axialCartanLieSubalgebra
        (nativeRootWeight j) := by
  apply InfoGeometry.Lie.CanonicalZornMathlibRootSpace.LinearEquiv.map_rootSpace_mem_of_cartan_normalizer
    i j e c hbracket hcartan hweight (rootDerivation i.1)
  intro H
  exact rootDerivation_bracket_eigen i H

end InfoGeometry.Algebra.Zorn.G2NativeWeylRootSpaceMembership
