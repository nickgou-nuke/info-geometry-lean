import InfoGeometry.Physics.AlgebraicTomitaTakesakiBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic Hestenes--Krein bilingual carrier

The real-form replacement for an analytic two-sided Hilbert-module claim is
the regular algebraic carrier.  It has a left `A` action and a right
`Aᵐᵒᵖ` action on the same underlying additive carrier.  The two actions
commute by associativity, while the opposite multiplication records the
reversal of the right-action word order.

This owner proves the carrier laws only.  It does not claim a Hilbert-module
completion or full Morita equivalence; those require separate evaluation and
coevaluation data.
-/

namespace InfoGeometry.Physics

open MulOpposite

variable {A : Type*} [Ring A]

def bilingualLeftAction (a x : A) : A := a * x

def bilingualRightOppositeAction (x : A) (b : Aᵐᵒᵖ) : A :=
  x * unop b

theorem bilingualLeftAction_unit (x : A) :
    bilingualLeftAction (1 : A) x = x := by
  simp [bilingualLeftAction]

theorem bilingualRightOppositeAction_unit (x : A) :
    bilingualRightOppositeAction x (1 : Aᵐᵒᵖ) = x := by
  simp [bilingualRightOppositeAction]

theorem bilingualLeftAction_assoc (a₁ a₂ x : A) :
    bilingualLeftAction a₁ (bilingualLeftAction a₂ x) =
      bilingualLeftAction (a₁ * a₂) x := by
  simp [bilingualLeftAction, mul_assoc]

theorem bilingualRightOppositeAction_assoc
    (x : A) (b₁ b₂ : Aᵐᵒᵖ) :
    bilingualRightOppositeAction
        (bilingualRightOppositeAction x b₂) b₁ =
      bilingualRightOppositeAction x (b₁ * b₂) := by
  simp [bilingualRightOppositeAction, mul_assoc]

theorem bilingual_left_right_commute
    (a x : A) (b : Aᵐᵒᵖ) :
    bilingualLeftAction a (bilingualRightOppositeAction x b) =
      bilingualRightOppositeAction (bilingualLeftAction a x) b := by
  simp [bilingualLeftAction, bilingualRightOppositeAction, mul_assoc]

theorem bilingual_right_word_order
    (x : A) (b₁ b₂ : Aᵐᵒᵖ) :
    bilingualRightOppositeAction x (b₁ * b₂) =
      bilingualRightOppositeAction
        (bilingualRightOppositeAction x b₂) b₁ := by
  symm
  exact bilingualRightOppositeAction_assoc x b₁ b₂

end InfoGeometry.Physics
