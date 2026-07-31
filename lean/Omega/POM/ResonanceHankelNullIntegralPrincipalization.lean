import Mathlib.Tactic
import Omega.POM.HankelSyndromeModuleKernelEqualsMultiples

namespace Omega.POM

/-- Paper label: `thm:pom-resonance-hankel-null-integral-principalization`. -/
theorem paper_pom_resonance_hankel_null_integral_principalization
    {n : ℕ} (nullModeKernel squareKernel multipleModule : Set (Fin n → ℤ))
    (nullMode_eq_squareKernel : nullModeKernel = squareKernel)
    (squareKernel_subset_multipleModule : squareKernel ⊆ multipleModule)
    (multipleModule_subset_squareKernel : multipleModule ⊆ squareKernel) :
    nullModeKernel = multipleModule := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxSquare : x ∈ squareKernel := by simpa [nullMode_eq_squareKernel] using hx
    exact squareKernel_subset_multipleModule hxSquare
  · intro x hx
    have hxSquare : x ∈ squareKernel :=
      multipleModule_subset_squareKernel hx
    simpa [nullMode_eq_squareKernel] using hxSquare

end Omega.POM
