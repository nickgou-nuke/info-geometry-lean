import proofs.D5IsotropicDiagonalLieEquiv
import proofs.A2SixStateMatrixRootBridge

/-! # Transport of the selected `A₂` root lines to diagonal complex `so(5,5)` -/

noncomputable section
namespace D5DiagonalRootTransport

open D5ComplexMatrixRootSpaces D5IsotropicDiagonalLieEquiv
open A2InsideD5RootSubsystem A2SixStateMatrixRootBridge

def isotropicCartan (h : Half → ℂ) : isotropicSO10 :=
  ⟨cartan h, cartan_isSplitOrthogonal h⟩

def isotropicA2Root (r : A2Root) : isotropicSO10 :=
  ⟨a2MatrixRoot r, a2MatrixRoot_isSplitOrthogonal r⟩

def diagonalCartan (h : Half → ℂ) : diagonalSO10 :=
  isotropicDiagonalLieEquiv (isotropicCartan h)

def diagonalA2Root (r : A2Root) : diagonalSO10 :=
  isotropicDiagonalLieEquiv (isotropicA2Root r)

theorem isotropic_root_eigen (h : Half → ℂ) (r : A2Root) :
    ⁅isotropicCartan h, isotropicA2Root r⁆ =
      rootWeight h r • isotropicA2Root r := by
  apply Subtype.ext
  exact a2MatrixRoot_eigen h r

theorem diagonalA2Root_ne_zero (r : A2Root) :
    diagonalA2Root r ≠ 0 := by
  intro hz
  have : isotropicA2Root r = 0 :=
    isotropicDiagonalLieEquiv.injective (by simpa [diagonalA2Root] using hz)
  exact a2MatrixRoot_ne_zero r (congrArg Subtype.val this)

/-- The Cartan weight equation survives the isotropic-to-diagonal change of
basis solely by Lie equivariance. -/
theorem diagonal_root_eigen (h : Half → ℂ) (r : A2Root) :
    ⁅diagonalCartan h, diagonalA2Root r⁆ =
      rootWeight h r • diagonalA2Root r := by
  change ⁅isotropicDiagonalLieEquiv (isotropicCartan h),
      isotropicDiagonalLieEquiv (isotropicA2Root r)⁆ =
    rootWeight h r • isotropicDiagonalLieEquiv (isotropicA2Root r)
  rw [← isotropicDiagonalLieEquiv.map_lie, isotropic_root_eigen,
    map_smul]

end D5DiagonalRootTransport
end noncomputable section
