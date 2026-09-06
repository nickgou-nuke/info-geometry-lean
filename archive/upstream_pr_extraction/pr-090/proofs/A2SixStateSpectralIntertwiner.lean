import proofs.HexIndexA2RootIntertwiner
import proofs.SixStateSpectralBridge

/-! # The `A₂` roots as the concrete six-state spectral basis labels -/

noncomputable section
namespace A2SixStateSpectralIntertwiner

open A2InsideD5RootSubsystem HexIndexA2RootIntertwiner
open HexagonalSixRootTiling SixStateSpectralBridge

def rootLabel (r : A2Root) : HexIndex := hexA2Equiv.symm r

def rootEigenvector (ω : ℂ) (r : A2Root) : State :=
  labelledVector ω (rootLabel r)

def rootEigenvalue (ω : ℂ) (r : A2Root) : ℂ :=
  labelledEigenvalue ω (rootLabel r)

theorem rootEigenvector_nonzero (ω : ℂ) (r : A2Root) :
    rootEigenvector ω r ≠ 0 :=
  labelledVector_nonzero ω (rootLabel r)

theorem rootEigenvector_eigen (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (r : A2Root) :
    TwoSheetThreeColorWeyl.sixfoldTriality.mulVec (rootEigenvector ω r) =
      rootEigenvalue ω r • rootEigenvector ω r :=
  labelledVector_eigen ω hω (rootLabel r)

@[simp] theorem rootLabel_weylReflection (r : A2Root) :
    rootLabel (weylAction colorWeylReflection r) =
      hexReflect (rootLabel r) := by
  change hexA2Equiv.symm (weylAction colorWeylReflection r) =
    hexReflect (hexA2Equiv.symm r)
  apply hexA2Equiv.injective
  rw [hexA2Equiv.apply_symm_apply]
  symm
  simpa using hexA2Equiv_hexReflect (hexA2Equiv.symm r)

@[simp] theorem rootLabel_weylCycle (r : A2Root) :
    rootLabel (weylAction colorWeylCycle r) =
      colorRotate (rootLabel r) := by
  change hexA2Equiv.symm (weylAction colorWeylCycle r) =
    colorRotate (hexA2Equiv.symm r)
  apply hexA2Equiv.injective
  rw [hexA2Equiv.apply_symm_apply]
  symm
  simpa using hexA2Equiv_colorRotate (hexA2Equiv.symm r)

/-- The concrete Pin operator realizes the `A₂` Weyl reflection on vectors. -/
  theorem pinTheta_rootEigenvector (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (r : A2Root) :
    pinTheta.mulVec (rootEigenvector ω r) =
      rootEigenvector ω (weylAction colorWeylReflection r) := by
  rw [rootEigenvector, rootEigenvector, pinTheta_labelledVector ω hω,
    rootLabel_weylReflection]

theorem a2_spectral_intertwining_packet (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    (∀ r, rootEigenvector ω r ≠ 0) ∧
    (∀ r, TwoSheetThreeColorWeyl.sixfoldTriality.mulVec
      (rootEigenvector ω r) = rootEigenvalue ω r • rootEigenvector ω r) ∧
    (∀ r, pinTheta.mulVec (rootEigenvector ω r) =
      rootEigenvector ω (weylAction colorWeylReflection r)) :=
  ⟨rootEigenvector_nonzero ω, rootEigenvector_eigen ω hω,
    pinTheta_rootEigenvector ω hω⟩

end A2SixStateSpectralIntertwiner
end noncomputable section
