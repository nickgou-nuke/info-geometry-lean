/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.CircularChiralGrading

/-!
# Grading interface for a split-octonion Furey extension

The paper-level `ℤ₂^5` grading is kept separate from the existing native Zorn
multiplication.  The latter is not closed on the eight basis labels, so this
file provides the grade carrier and the precise compatibility contract rather
than asserting an unavailable basis product.
-/

namespace InfoGeometry.Algebra.SplitOctonionFureyGrading

open InfoGeometry.Algebra.CircularChiralCausalConeBasis
open InfoGeometry.Algebra.CircularChiralGrading

/-- Five binary grading labels. -/
abbrev FureyGrade := Fin 5 → ZMod 2

/-- A canonical lift of the existing chiral parity to five binary labels.
Only the first coordinate is populated; the remaining coordinates are left
available for future independent division-algebra labels. -/
def parityGrade (b : ChiralBasis) : FureyGrade :=
  fun i => if i = 0 then chiralParity b else 0

@[simp] theorem parityGrade_zero_coordinate (b : ChiralBasis) :
    parityGrade b 0 = chiralParity b := by
  simp [parityGrade]

@[simp] theorem parityGrade_succ_coordinate (b : ChiralBasis) (i : Fin 4) :
    parityGrade b i.succ = 0 := by
  simp [parityGrade]

/-- The exact contract required of a homogeneous split-octonion product. -/
structure HomogeneousProduct (X : Type*) where
  grade : X → FureyGrade
  product : X → X → X
  product_grade : ∀ x y, grade (product x y) = grade x + grade y

theorem parityGrade_add_iff (a b : ChiralBasis)
    (h : chiralParity a + chiralParity b = chiralParity a) :
    parityGrade a + parityGrade b = parityGrade a := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [parityGrade, h]
  · simp [parityGrade, hi]

/-- Exchange of the two Peirce sheets on the existing chiral basis. -/
def chiralBasisSectorExchange : ChiralBasis → ChiralBasis
  | .uPlus => .uMinus
  | .uMinus => .uPlus
  | .up i => .down i
  | .down i => .up i

@[simp] theorem chiralBasisSectorExchange_involutive (b : ChiralBasis) :
    chiralBasisSectorExchange (chiralBasisSectorExchange b) = b := by
  cases b <;> rfl

theorem parityGrade_sectorExchange (b : ChiralBasis) :
    parityGrade (chiralBasisSectorExchange b) = parityGrade b := by
  cases b <;> rfl

end InfoGeometry.Algebra.SplitOctonionFureyGrading
