import proofs.KleinSixStateAssociatedQuotient
import proofs.A2SixStateSpectralIntertwiner

/-!
# A certified flat-band Hamiltonian over the Klein Brillouin quotient

This is the minimal continuous and glide-equivariant Hamiltonian.  Its six
`A₂`-labelled bands are flat and degenerate; no dispersive cone claim is made.
-/

noncomputable section
namespace KleinFlatBandHamiltonian

open KleinBrillouinBase KleinBottleOrbitQuotient KleinSixStateBundle
open A2InsideD5RootSubsystem A2SixStateSpectralIntertwiner
open TwoSheetThreeColorWeyl SixStateSpectralBridge

/-- The identity Hamiltonian, used as the canonical flat-band base point. -/
def flatHamiltonian (_ : BrillouinTorus) : M6C := 1

theorem flatHamiltonian_continuous : Continuous flatHamiltonian :=
  continuous_const

theorem flatHamiltonian_glide_equivariant (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    IsGlideEquivariant torusGlide flatHamiltonian := by
  intro k
  simp only [flatHamiltonian]
  rw [Matrix.mul_one, theta_sq ω hω]

/-- Every concrete `A₂` root vector is a band vector of eigenvalue one. -/
theorem flatHamiltonian_root_band (ω : ℂ) (k : BrillouinTorus)
    (r : A2Root) :
    (flatHamiltonian k).mulVec (rootEigenvector ω r) =
      (1 : ℂ) • rootEigenvector ω r := by
  simp [flatHamiltonian]

/-- The flat Hamiltonian descends as an operator-valued function on the orbit
base because it is constant on glide orbits. -/
def quotientHamiltonian : KleinBrillouinQuotient → M6C :=
  Quotient.lift flatHamiltonian (by
    intro x y h
    rcases h with rfl | h
    · rfl
    · simp [flatHamiltonian])

@[simp] theorem quotientHamiltonian_mk (k : BrillouinTorus) :
    quotientHamiltonian (quotientMap k) = flatHamiltonian k := rfl

theorem quotientHamiltonian_continuous : Continuous quotientHamiltonian := by
  apply continuous_quot_lift
  exact flatHamiltonian_continuous

theorem flat_band_packet (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    Continuous flatHamiltonian ∧
    IsGlideEquivariant torusGlide flatHamiltonian ∧
    (∀ k r, (flatHamiltonian k).mulVec (rootEigenvector ω r) =
      (1 : ℂ) • rootEigenvector ω r) :=
  ⟨flatHamiltonian_continuous, flatHamiltonian_glide_equivariant ω hω,
    flatHamiltonian_root_band ω⟩

end KleinFlatBandHamiltonian
end noncomputable section
