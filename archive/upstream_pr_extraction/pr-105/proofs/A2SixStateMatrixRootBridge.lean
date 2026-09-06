import proofs.D5ComplexMatrixRootSpaces
import proofs.A2SixStateSpectralIntertwiner

/-! # One `A₂` label, one six-state eigenline, one `D₅` matrix root line -/

noncomputable section
namespace A2SixStateMatrixRootBridge

open A2InsideD5RootSubsystem A2SixStateSpectralIntertwiner
open D5ComplexMatrixRootSpaces

def rootHalf (i : Fin 3) : Half := ⟨i, by omega⟩

def a2MatrixRoot (r : A2Root) : CM10 :=
  differenceRootMatrix (rootHalf r.1.1) (rootHalf r.1.2)

theorem rootHalf_injective : Function.Injective rootHalf := by
  intro i j h
  exact Fin.ext (Fin.mk.inj h)

theorem a2MatrixRoot_isSplitOrthogonal (r : A2Root) :
    IsSplitOrthogonal (a2MatrixRoot r) :=
  differenceRoot_isSplitOrthogonal _ _
    (fun h => r.property (rootHalf_injective h))

theorem a2MatrixRoot_ne_zero (r : A2Root) : a2MatrixRoot r ≠ 0 :=
  differenceRootMatrix_ne_zero
    (fun h => r.property (rootHalf_injective h))

def rootWeight (h : Half → ℂ) (r : A2Root) : ℂ :=
  h (rootHalf r.1.1) - h (rootHalf r.1.2)

theorem a2MatrixRoot_eigen (h : Half → ℂ) (r : A2Root) :
    commutator (cartan h) (a2MatrixRoot r) =
      rootWeight h r • a2MatrixRoot r :=
  cartan_bracket_difference h _ _

/-- The independent spectral and matrix-root realizations indexed by the same
oriented `A₂` root. -/
structure RootRealization (ω : ℂ) where
  label : A2Root
  spectralVector : SixStateSpectralBridge.State
  matrixRoot : CM10

def realizeRoot (ω : ℂ) (r : A2Root) : RootRealization ω where
  label := r
  spectralVector := rootEigenvector ω r
  matrixRoot := a2MatrixRoot r

theorem realization_packet (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (h : Half → ℂ) (r : A2Root) :
    (realizeRoot ω r).spectralVector ≠ 0 ∧
    TwoSheetThreeColorWeyl.sixfoldTriality.mulVec
      (realizeRoot ω r).spectralVector =
        rootEigenvalue ω r • (realizeRoot ω r).spectralVector ∧
    IsSplitOrthogonal (realizeRoot ω r).matrixRoot ∧
    (realizeRoot ω r).matrixRoot ≠ 0 ∧
    commutator (cartan h) (realizeRoot ω r).matrixRoot =
      rootWeight h r • (realizeRoot ω r).matrixRoot :=
  ⟨rootEigenvector_nonzero ω r, rootEigenvector_eigen ω hω r,
    a2MatrixRoot_isSplitOrthogonal r, a2MatrixRoot_ne_zero r,
    a2MatrixRoot_eigen h r⟩

end A2SixStateMatrixRootBridge
end noncomputable section
