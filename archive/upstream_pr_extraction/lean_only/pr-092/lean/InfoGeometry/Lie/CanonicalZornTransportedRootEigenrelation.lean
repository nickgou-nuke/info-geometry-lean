import InfoGeometry.Lie.CanonicalZornDerivationCarrierEquiv
import InfoGeometry.Lie.CanonicalZornMathlibRootSpace

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornTransportedRootEigenrelation

open InfoGeometry.Lie.CanonicalZornDerivationCarrierEquiv
open InfoGeometry.Lie.CanonicalZornMathlibRootSpace
open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

theorem rootDerivation_bracket_eigen
    (i : InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.nonzeroIndex)
    (H : axialCartanLieSubalgebra) :
    ⁅(nativeToMathlib H.1 : Mathlib), rootDerivation i.1⁆ =
      nativeRootWeight i H • (rootDerivation i.1 : Mathlib) := by
  let k := axialCartanLieEquiv.symm H
  have h := adCartan_rootDerivation k i.1
  have hk : axialCartanLieEquiv k = H := by simp [k]
  have hs : nativeToMathlib.symm (rootDerivation i.1) = rootDerivation i.1 := by
    apply nativeToMathlib.injective
    simp
  calc
    ⁅(nativeToMathlib H.1 : Mathlib), rootDerivation i.1⁆ =
        ⁅nativeToMathlib (axialCartanLieEquiv k),
          nativeToMathlib (nativeToMathlib.symm (rootDerivation i.1))⁆ := by
      rw [hk, nativeToMathlib.apply_symm_apply]
    _ = nativeToMathlib ⁅axialCartanLieEquiv k,
          nativeToMathlib.symm (rootDerivation i.1)⁆ := by
      symm
      exact nativeToMathlib.map_lie _ _
    _ = nativeToMathlib (nativeRootWeight i H • rootDerivation i.1) := by
      rw [hs]
      simpa [nativeRootWeight, k] using congrArg nativeToMathlib h
    _ = nativeRootWeight i H • (rootDerivation i.1 : Mathlib) := by
      simp only [map_smul, nativeToMathlib_apply]

end InfoGeometry.Lie.CanonicalZornTransportedRootEigenrelation
