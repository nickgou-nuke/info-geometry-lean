import InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornMathlibBridge

/-!
# Native root-bracket coefficient consequences

This file transports the intrinsic Cartan root-space vanishing theorem to the
coefficient readout.  It deliberately does not identify the coefficients with
an external CAS table; that requires a separate basis-alignment theorem.
-/

namespace InfoGeometry.Lie.CanonicalZornG2RootBracketCoefficients

open InfoGeometry.Lie.CanonicalZornG2NativeMatrixExport
open InfoGeometry.Lie.CanonicalZornMathlibBridge
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornCartanRootSystem
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

theorem rootBracketCoefficient_zero_of_sum_not_nativeRootWeight
    (i j : nonzeroIndex)
    (hχ : ∀ k : Fin 14,
      (fun x : axialCartanLieSubalgebra =>
        rootWeight k (axialCartanLieEquiv.symm x)) ≠
          (nativeRootWeight i + nativeRootWeight j))
    (k : Fin 14) :
    rootBracketCoefficient i.1 j.1 k = 0 := by
  unfold rootBracketCoefficient
  rw [rootDerivation_bracket_eq_zero_of_sum_not_nativeRootWeight i j hχ]
  simp

theorem rootBracketCoefficient_eq_of_bracket_eq_smul
    (i j k : Fin 14) (c : ℝ)
    (hbr : ⁅rootDerivation i, rootDerivation j⁆ = c • rootDerivation k) :
    rootBracketCoefficient i j k = c := by
  rw [rootBracketCoefficient_eq_basis_repr, hbr]
  rw [← rootDerivationBasis_apply k]
  rw [map_smul]
  rw [rootDerivationBasis.repr_self]
  simp [smul_eq_mul]

end InfoGeometry.Lie.CanonicalZornG2RootBracketCoefficients
