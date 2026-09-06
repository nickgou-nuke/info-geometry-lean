import proofs.D5DiagonalComplexification
import proofs.A2SixStateMatrixRootBridge

/-! # Explicit transport of the selected complex `D₅` root lines into TKK coordinates -/

noncomputable section
namespace D5TKKRootTransport

open D5ComplexMatrixRootSpaces D5IsotropicDiagonalLieEquiv
open D5DiagonalComplexification TKK55Complexification
open A2InsideD5RootSubsystem A2SixStateMatrixRootBridge
open A2SixStateSpectralIntertwiner

/-- The complete certified chain
`isotropic matrices → diagonal matrices → scalar extension → complex TKK`. -/
def isotropicTkkLieEquiv : isotropicSO10 ≃ₗ⁅ℂ⁆ ComplexTKK :=
  isotropicDiagonalLieEquiv.trans <|
    reindexDiagonalLieEquiv.trans <|
      diagonalComplexificationLieEquiv.symm.trans
        complexTkkDiagonalLieEquiv.symm

def tkkCartanElement (h : Half → ℂ) : ComplexTKK :=
  isotropicTkkLieEquiv ⟨cartan h, cartan_isSplitOrthogonal h⟩

def tkkA2RootVector (r : A2Root) : ComplexTKK :=
  isotropicTkkLieEquiv ⟨a2MatrixRoot r, a2MatrixRoot_isSplitOrthogonal r⟩

theorem tkkA2RootVector_ne_zero (r : A2Root) :
    tkkA2RootVector r ≠ 0 := by
  intro h
  have hs : (⟨a2MatrixRoot r, a2MatrixRoot_isSplitOrthogonal r⟩ :
      isotropicSO10) = 0 := isotropicTkkLieEquiv.injective (by
        simpa [tkkA2RootVector] using h)
  exact a2MatrixRoot_ne_zero r (congrArg Subtype.val hs)

/-- The `D₅` Cartan eigenvalue equation in native complexified TKK coordinates. -/
theorem tkk_root_eigenvalue (h : Half → ℂ) (r : A2Root) :
    ⁅tkkCartanElement h, tkkA2RootVector r⁆ =
      rootWeight h r • tkkA2RootVector r := by
  change ⁅isotropicTkkLieEquiv
      ⟨cartan h, cartan_isSplitOrthogonal h⟩,
    isotropicTkkLieEquiv
      ⟨a2MatrixRoot r, a2MatrixRoot_isSplitOrthogonal r⟩⁆ = _
  rw [← isotropicTkkLieEquiv.map_lie]
  change isotropicTkkLieEquiv _ =
    rootWeight h r • isotropicTkkLieEquiv
      (⟨a2MatrixRoot r, a2MatrixRoot_isSplitOrthogonal r⟩ : isotropicSO10)
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  exact a2MatrixRoot_eigen h r

/-- One oriented `A₂` label simultaneously supplies its nonzero six-state
eigenvector and its nonzero TKK root vector with the same Cartan weight. -/
theorem sixState_tkk_root_packet (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (h : Half → ℂ) (r : A2Root) :
    rootEigenvector ω r ≠ 0 ∧
    TwoSheetThreeColorWeyl.sixfoldTriality.mulVec (rootEigenvector ω r) =
      rootEigenvalue ω r • rootEigenvector ω r ∧
    tkkA2RootVector r ≠ 0 ∧
    ⁅tkkCartanElement h, tkkA2RootVector r⁆ =
      rootWeight h r • tkkA2RootVector r :=
  ⟨rootEigenvector_nonzero ω r, rootEigenvector_eigen ω hω r,
    tkkA2RootVector_ne_zero r, tkk_root_eigenvalue h r⟩

end D5TKKRootTransport
end noncomputable section
