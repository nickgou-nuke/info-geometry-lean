/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.CircularChiralGrading
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

/-! The circular Peirce ordering is transported to the existing chiral basis;
this is an index equivalence, not a new algebraic carrier. -/

def circularPeirceToChiral : Fin 8 ≃ ChiralBasis where
  toFun
    | 0 => ChiralBasis.uPlus
    | 1 => ChiralBasis.up 0
    | 2 => ChiralBasis.up 1
    | 3 => ChiralBasis.up 2
    | 4 => ChiralBasis.uMinus
    | 5 => ChiralBasis.down 0
    | 6 => ChiralBasis.down 1
    | 7 => ChiralBasis.down 2
    | _ => ChiralBasis.uPlus
  invFun
    | ChiralBasis.uPlus => 0
    | ChiralBasis.up i => ⟨i.val + 1, by omega⟩
    | ChiralBasis.uMinus => 4
    | ChiralBasis.down i => ⟨i.val + 5, by omega⟩
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro b
    cases b with
    | uPlus => rfl
    | uMinus => rfl
    | up i => fin_cases i <;> rfl
    | down i => fin_cases i <;> rfl

def circularParityGrade (i : Fin 8) : FureyGrade :=
  parityGrade (circularPeirceToChiral i)

@[simp] theorem circularParityGrade_zero :
    circularParityGrade 0 = parityGrade ChiralBasis.uPlus := rfl

@[simp] theorem circularParityGrade_four :
    circularParityGrade 4 = parityGrade ChiralBasis.uMinus := rfl

theorem circularParityGrade_sector (i : Fin 8) :
    circularParityGrade i 0 =
      if i = 0 ∨ i = 4 then 0 else 1 := by
  fin_cases i <;> simp [circularParityGrade, circularPeirceToChiral,
    parityGrade, chiralParity]

def circularSectorExchangeIndex : Fin 8 → Fin 8
  | 0 => 4
  | 1 => 5
  | 2 => 6
  | 3 => 7
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | _ => 0

@[simp] theorem circularSectorExchangeIndex_involutive (i : Fin 8) :
    circularSectorExchangeIndex (circularSectorExchangeIndex i) = i := by
  fin_cases i <;> rfl

theorem circularPeirceToChiral_sectorExchange (i : Fin 8) :
    circularPeirceToChiral (circularSectorExchangeIndex i) =
      chiralBasisSectorExchange (circularPeirceToChiral i) := by
  fin_cases i <;> rfl

theorem circularParityGrade_sectorExchange_index (i : Fin 8) :
    circularParityGrade (circularSectorExchangeIndex i) =
      circularParityGrade i := by
  rw [circularParityGrade, circularParityGrade,
    circularPeirceToChiral_sectorExchange, parityGrade_sectorExchange]

end InfoGeometry.Algebra.SplitOctonionFureyGrading
