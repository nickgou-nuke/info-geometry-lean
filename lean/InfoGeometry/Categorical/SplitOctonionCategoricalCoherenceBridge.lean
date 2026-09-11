import InfoGeometry.Canonical.SplitOctonionZ2ThreeCochainBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib

/-!
# Categorical Coherence of Split Octonion Basis

This module establishes the quasi-tensor leaf / categorical coherence 
of the split octonion algebra's `(ZMod 2)^3`-graded basis. 

It defines the Mac Lane pentagon and hexagon equations structurally
over the graded components, and checks them against the native 
`splitAssociativityDefect` and `splitExchangeSign` extracted from the 
split octonion multiplication table.

This provides the exact categorical mapping requested by the 
coherence-aware tensor compiler architecture.
-/

namespace InfoGeometry.Categorical.SplitOctonionCategoricalCoherenceBridge

open InfoGeometry.Canonical.SplitOctonionZ2ThreeCochainBridge

abbrev splitAssociativityDefect : Grade → Grade → Grade → ℚ :=
  associatorCochain

abbrev splitExchangeSign : Grade → Grade → ℚ :=
  exchangeCochain

/-- The categorical Mac Lane pentagon equation on the skeletal `(ZMod 2)^3` grades.
This is exactly the multiplicative 3-cocycle condition. -/
def skeletalPentagonEquation (ϕ : Grade → Grade → Grade → ℚ) : Prop :=
  ∀ X Y Z W : Grade,
    ϕ Y Z W * ϕ X (gradeAdd Y Z) W * ϕ X Y Z =
    ϕ (gradeAdd X Y) Z W * ϕ X Y (gradeAdd Z W)

/-- 
The pentagon equation holds for the split octonionic associativity defect. 
This elevates the local algebraic defect into a categorical associator.
-/
theorem splitOctonion_pentagon_holds :
    skeletalPentagonEquation splitAssociativityDefect := by
  intro X Y Z W
  exact native_associator_three_cocycle X Y Z W

/-- The forward Mac Lane hexagon equation for a braiding `R` and associator `ϕ`. -/
def skeletalHexagonForward (ϕ : Grade → Grade → Grade → ℚ) (R : Grade → Grade → ℚ) : Prop :=
  ∀ X Y Z : Grade,
    R X (gradeAdd Y Z) * ϕ Y Z X =
    ϕ Y X Z * R X Y * ϕ X Y Z * R X Z

/-- The reverse Mac Lane hexagon equation for a braiding `R` and associator `ϕ`. -/
def skeletalHexagonReverse (ϕ : Grade → Grade → Grade → ℚ) (R : Grade → Grade → ℚ) : Prop :=
  ∀ X Y Z : Grade,
    R (gradeAdd X Y) Z * ϕ Z X Y =
    ϕ X Z Y * R Y Z * ϕ X Y Z * R X Z

/-- 
The categorical hexagon consistency equations for the split octonionic 
exchange sign and associativity defect.
-/
theorem splitOctonion_hexagon_holds :
    skeletalHexagonForward splitAssociativityDefect splitExchangeSign ∧
    skeletalHexagonReverse splitAssociativityDefect splitExchangeSign := by
  constructor
  · intro X Y Z
    revert X Y Z
    native_decide
  · intro X Y Z
    revert X Y Z
    native_decide

end InfoGeometry.Categorical.SplitOctonionCategoricalCoherenceBridge
