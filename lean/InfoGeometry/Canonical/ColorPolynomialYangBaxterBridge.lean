import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionThreeColorModularCl11

/-!
# External three-colour braid action

The carrier here is a finite tensor-function space.  The operators below are
not multiplication in the split-octonion or Zorn algebra.
-/

namespace InfoGeometry.Canonical.ThreeColorPolynomialYangBaxterBridge

open InfoGeometry.Canonical
open SplitOctonionColour

abbrev ColorTensor2 := SplitOctonionColour → SplitOctonionColour → ℚ
abbrev ColorTensor3 :=
  SplitOctonionColour → SplitOctonionColour → SplitOctonionColour → ℚ

def R_swap (T : ColorTensor2) : ColorTensor2 :=
  fun c₁ c₂ => T c₂ c₁

@[simp] theorem R_swap_quadratic_relation (T : ColorTensor2) :
    R_swap (R_swap T) = T := by
  rfl

def R12 (T : ColorTensor3) : ColorTensor3 :=
  fun c₁ c₂ c₃ => T c₂ c₁ c₃

def R23 (T : ColorTensor3) : ColorTensor3 :=
  fun c₁ c₂ c₃ => T c₁ c₃ c₂

theorem R_swap_yang_baxter (T : ColorTensor3) :
    R12 (R23 (R12 T)) = R23 (R12 (R23 T)) := by
  funext c₁ c₂ c₃
  rfl

def colorShift : SplitOctonionColour → SplitOctonionColour
  | red => green
  | green => blue
  | blue => red

def tensorAction (M : ColorTensor2) : ColorTensor2 :=
  fun c₁ c₂ => M (colorShift c₁) (colorShift c₂)

theorem R_swap_color_equivariant (M : ColorTensor2) :
    R_swap (tensorAction M) = tensorAction (R_swap M) := by
  funext c₁ c₂
  rfl

end InfoGeometry.Canonical.ThreeColorPolynomialYangBaxterBridge
