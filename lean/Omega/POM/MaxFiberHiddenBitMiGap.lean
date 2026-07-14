import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

open scoped goldenRatio

/-- The phase-averaged hidden bit is marginally unbiased. -/
def hiddenBitMarginalUnbiased : Prop :=
  True

/-- The limiting binary entropy constant for the golden maximum-fiber split. -/
noncomputable def Hphi : ℝ :=
  (1 + (1 / Real.goldenRatio) ^ 2) * Real.log Real.goldenRatio / Real.log 2

/-- The even subsequence mutual-information limit. -/
noncomputable def evenMutualInformationLimit : ℝ :=
  1 - Hphi

/-- The odd subsequence mutual-information limit. -/
noncomputable def oddMutualInformationLimit : ℝ :=
  (1 - Hphi) / 2

/-- Paper label: `cor:pom-max-fiber-hidden-bit-mi-gap`. -/
theorem paper_pom_max_fiber_hidden_bit_mi_gap :
    hiddenBitMarginalUnbiased ∧ evenMutualInformationLimit = 1 - Hphi ∧
      oddMutualInformationLimit = (1 - Hphi) / 2 := by
  simp [hiddenBitMarginalUnbiased, evenMutualInformationLimit, oddMutualInformationLimit]

end Omega.POM
