import InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
import InfoGeometry.Lie.SplitOctonionStandardDerivationRootBridge

/-!
# Cartan derivations as native inner derivations

The two Cartan directions are not new generators: they are the already
proved `U₀,V₀` and `U₁,V₁` standard derivations, transported to the native
Zorn-vector derivation carrier.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2CartanDerivationPairRealization

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Lie.SplitOctonionStandardDerivationRootBridge
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

theorem canonicalToVector_standard_U0_V0 :
    canonicalToVectorDerivation
        (canonicalStandardDerivationOfCanonical
          (canonicalU 0) (canonicalV 0)) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 0))
        (canonicalVectorEquiv (canonicalV 0)) := by
  apply vectorCanonicalLinearEquiv.injective
  simp only [vectorCanonicalLinearEquiv, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact (vector_inner_to_canonical
    (canonicalVectorEquiv (canonicalU 0))
    (canonicalVectorEquiv (canonicalV 0))).symm

theorem cartanDerivation_pair_realization_U0_V0 :
    canonicalToVectorDerivation
        (canonicalStandardDerivationOfCanonical
          (canonicalU 0) (canonicalV 0)) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 0))
        (canonicalVectorEquiv (canonicalV 0)) :=
  canonicalToVector_standard_U0_V0

theorem canonicalToVector_standard_U1_V1 :
    canonicalToVectorDerivation
        (canonicalStandardDerivationOfCanonical
          (canonicalU 1) (canonicalV 1)) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalU 1))
        (canonicalVectorEquiv (canonicalV 1)) := by
  apply vectorCanonicalLinearEquiv.injective
  simp only [vectorCanonicalLinearEquiv, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact (vector_inner_to_canonical
    (canonicalVectorEquiv (canonicalU 1))
    (canonicalVectorEquiv (canonicalV 1))).symm

theorem canonicalToVector_standard_V0_U0 :
    canonicalToVectorDerivation
        (canonicalStandardDerivationOfCanonical
          (canonicalV 0) (canonicalU 0)) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalV 0))
        (canonicalVectorEquiv (canonicalU 0)) := by
  apply vectorCanonicalLinearEquiv.injective
  simp only [vectorCanonicalLinearEquiv, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact (vector_inner_to_canonical
    (canonicalVectorEquiv (canonicalV 0))
    (canonicalVectorEquiv (canonicalU 0))).symm

theorem canonicalToVector_standard_V2_U2 :
    canonicalToVectorDerivation
        (canonicalStandardDerivationOfCanonical
          (canonicalV 2) (canonicalU 2)) =
      NativeStanDerivationBilinear.innerDerivation
        (canonicalVectorEquiv (canonicalV 2))
        (canonicalVectorEquiv (canonicalU 2)) := by
  apply vectorCanonicalLinearEquiv.injective
  simp only [vectorCanonicalLinearEquiv, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact (vector_inner_to_canonical
    (canonicalVectorEquiv (canonicalV 2))
    (canonicalVectorEquiv (canonicalU 2))).symm

end InfoGeometry.Algebra.Zorn.G2CartanDerivationPairRealization
