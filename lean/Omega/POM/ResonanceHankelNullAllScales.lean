import Mathlib.Tactic
import Omega.POM.ResonanceHankelNullIntegralPrincipalization

namespace Omega.POM

/-- Concrete all-scale resonance-window package: the length-`m` null-mode kernel is compared to
the square Hankel kernel on the same coefficient space, and the rank count is recorded through the
truncated-multiple parameter count `m - d_q`. -/
structure ResonanceHankelNullAllScalesData where
  m : ℕ
  L : ℕ
  d_q : ℕ
  hd : d_q + 1 ≤ m
  hLm : m ≤ L
  nullModeKernel : Set (Fin m → ℤ)
  squareKernel : Set (Fin m → ℤ)
  multipleModule : Set (Fin m → ℤ)
  nullity : ℕ
  multipleRank : ℕ
  nullMode_eq_squareKernel : nullModeKernel = squareKernel
  squareKernel_subset_multipleModule : squareKernel ⊆ multipleModule
  multipleModule_subset_squareKernel : multipleModule ⊆ squareKernel
  nullity_eq_multipleRank_of_eq :
    nullModeKernel = multipleModule → nullity = multipleRank
  multipleRank_eq_truncationCount : multipleRank = m - d_q

namespace ResonanceHankelNullAllScalesData

/-- Paper conclusion at truncation length `m`: the null modes equal the truncated multiples. -/
def nullModesEqMultiplesAtAllScales (D : ResonanceHankelNullAllScalesData) : Prop :=
  D.nullModeKernel = D.multipleModule

/-- The rank of the length-`m` null-mode module is the truncated-multiple parameter count. -/
def rankNullModesAtAllScales (D : ResonanceHankelNullAllScalesData) : Prop :=
  D.nullity = D.m - D.d_q

end ResonanceHankelNullAllScalesData

open ResonanceHankelNullAllScalesData

/-- Paper label: `prop:pom-resonance-hankel-null-all-scales`. -/
theorem paper_pom_resonance_hankel_null_all_scales (D : ResonanceHankelNullAllScalesData) :
    D.nullModesEqMultiplesAtAllScales ∧ D.rankNullModesAtAllScales := by
  have hEq : D.nullModesEqMultiplesAtAllScales := by
    simpa [ResonanceHankelNullAllScalesData.nullModesEqMultiplesAtAllScales] using
      paper_pom_resonance_hankel_null_integral_principalization D.nullModeKernel
        D.squareKernel D.multipleModule D.nullMode_eq_squareKernel
        D.squareKernel_subset_multipleModule D.multipleModule_subset_squareKernel
  have hRank : D.rankNullModesAtAllScales := by
    rw [ResonanceHankelNullAllScalesData.rankNullModesAtAllScales]
    rw [D.nullity_eq_multipleRank_of_eq hEq, D.multipleRank_eq_truncationCount]
  exact ⟨hEq, hRank⟩

end Omega.POM
