import InfoGeometry.OperatorAlgebra.ChiralCuntzBraidedSuperchargeBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ChiralZornBasisSoldering

/-!
# The ordinary SUSY product versus the chiral Cayley product

The matrix-unit supercharges and the split-Zorn chiral basis carry two
different products.  Ordinary matrix composition is the associative SUSY
envelope: same-sheet odd channels square to zero.  The native Zorn product is
the Cayley layer: its same-sheet products transfer the oriented spin channel
to the opposite sheet.  This file records that distinction without identifying
the braid witness or a central charge with either product.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralCuntzCayleySUSY

open InfoGeometry.OperatorAlgebra.ChiralCuntzSUSYNative
open InfoGeometry.Algebra

/-! ## Associative matrix envelope -/

theorem qPlus_mul_qPlus_zero {A : Type*} [Semiring A] (a b : A) :
    qPlus a * qPlus b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qPlus, Matrix.mul_apply, Fin.sum_univ_two]

theorem qMinus_mul_qMinus_zero {A : Type*} [Semiring A] (a b : A) :
    qMinus a * qMinus b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem ordinary_same_sheet_zero {A : Type*} [Semiring A] (a b : A) :
    qPlus a * qPlus b = 0 ∧ qMinus a * qMinus b = 0 :=
  ⟨qPlus_mul_qPlus_zero a b, qMinus_mul_qMinus_zero a b⟩

/-! ## Native Cayley channel -/

theorem cayley_plus_spin_transfer :
    chiralSigmaPlus 0 * chiralSigmaPlus 1 = chiralSigmaMinus 2 := by
  exact chiralSigmaPlus_zero_mul_one

theorem cayley_minus_spin_transfer :
    chiralSigmaMinus 0 * chiralSigmaMinus 1 =
      ZornMatrix.sub (0 : SplitZornC) (chiralSigmaPlus 2) := by
  exact chiralSigmaMinus_zero_mul_one

theorem cayley_mixed_scalar_channel (i j : Fin 3) :
    chiralSigmaPlus i * chiralSigmaMinus j =
      if i = j then chiralUPlus else 0 := by
  exact chiralSigmaPlus_mul_minus i j

theorem cayley_mixed_scalar_channel_opposite (i j : Fin 3) :
    chiralSigmaMinus i * chiralSigmaPlus j =
      if i = j then chiralUMinus else 0 := by
  exact chiralSigmaMinus_mul_plus i j

/-! ## The two products are complementary, not interchangeable -/

theorem cayley_susy_product_separation :
    qPlus (1 : ℂ) * qPlus (1 : ℂ) = 0 ∧
    chiralSigmaPlus 0 * chiralSigmaPlus 1 = chiralSigmaMinus 2 ∧
    chiralSigmaPlus 0 * chiralSigmaMinus 0 = chiralUPlus := by
  refine ⟨qPlus_sq 1, cayley_plus_spin_transfer, ?_⟩
  simpa using (cayley_mixed_scalar_channel 0 0)

end InfoGeometry.OperatorAlgebra.ChiralCuntzCayleySUSY
