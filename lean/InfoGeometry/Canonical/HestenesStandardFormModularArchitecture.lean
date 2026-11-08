import InfoGeometry.Canonical.HestenesHermitianMatrixBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteHestenesModularOperator

/-!
# The finite Hestenes standard-form modular architecture

The Hestenes Hermitian adjoint is an anti-involution on the even Clifford
algebra.  After the finite Pauli/M₂(ℂ) standard-form realization it is the
Tomita modular conjugation on the Hilbert--Schmidt carrier.  This owner does
not identify it with the Dirac adjoint of a spinor covector.
-/

noncomputable section
namespace HestenesStandardFormModularArchitecture

open HestenesCl14 HestenesHermitianAdjoint
open HestenesHermitianMatrixBridge
open HestenesEvenPauliEquiv HestenesPauliSheetBridge
open FiniteHestenesTomitaBridge FiniteHestenesModularOperator

abbrev EvenAlgebra := ClPlus14
abbrev StandardCarrier := HS2

/-- The Hestenes adjoint, realized as finite standard-form Tomita `J`. -/
def hestenesTomitaJ : EvenAlgebra → EvenAlgebra := cliffordTomita

@[simp] theorem hestenesTomitaJ_apply (x : EvenAlgebra) :
    hestenesTomitaJ x = cliffordTomita x := rfl

@[simp] theorem hestenesTomitaJ_involutive (x : EvenAlgebra) :
    hestenesTomitaJ (hestenesTomitaJ x) = x :=
  cliffordTomita_involutive x

@[simp] theorem matrixTomita_conj_smul (z : ℂ) (X : StandardCarrier) :
    matrixTomita (z • X) = starRingEnd ℂ z • matrixTomita X := by
  simp [matrixTomita, Matrix.conjTranspose_smul]

theorem hestenesAdjoint_is_standard_form_Tomita (x : EvenAlgebra) :
    hestenesAdjoint x = hestenesTomitaJ x :=
  HestenesHermitianMatrixBridge.hestenesAdjoint_eq_cliffordTomita x

theorem hestenesAdjoint_liftComplexCoeff (z : ℂ) (x : EvenAlgebra) :
    hestenesAdjoint (liftComplexCoeff z x) =
      liftComplexCoeff (starRingEnd ℂ z) (hestenesAdjoint x) := by
  apply clPlusPauliAlgEquiv.injective
  rw [clPlusPauliAlgEquiv_hestenesAdjoint]
  change Matrix.conjTranspose
      (clPlusToPauli (liftComplexCoeff z x)) =
    clPlusToPauli (liftComplexCoeff (starRingEnd ℂ z) (hestenesAdjoint x))
  simp only [clPlusToPauli_liftComplexCoeff,
    clPlusToPauli_hestenesAdjoint]
  rw [Matrix.conjTranspose_smul]
  rfl

theorem standard_form_left_right_exchange (a x : EvenAlgebra) :
    hestenesTomitaJ (cliffordLeftAction a (hestenesTomitaJ x)) =
      cliffordRightAction x (hestenesTomitaJ a) :=
  cliffordTomita_left_to_right a x

theorem matrix_standard_form_left_right_exchange (A X : StandardCarrier) :
    matrixTomita (matrixLeftAction A (matrixTomita X)) =
      matrixRightAction X (matrixTomita A) :=
  matrixTomita_left_to_right A X

theorem standard_form_modular_reversal
    (d : ModularDatum) (X : StandardCarrier) :
    matrixTomita (d.delta (matrixTomita X)) = d.deltaInv X :=
  d.tomita_delta_tomita X

theorem hestenes_standard_form_modular_reversal
    (d : ModularDatum) (x : EvenAlgebra) :
    cliffordTomita (d.cliffordDelta (cliffordTomita x)) =
      d.cliffordDeltaInv x :=
  d.cliffordTomita_delta_tomita x

theorem hestenes_standard_form_packet :
    (∀ x : EvenAlgebra,
      hestenesAdjoint x = hestenesTomitaJ x) ∧
    (∀ x : EvenAlgebra,
      hestenesTomitaJ (hestenesTomitaJ x) = x) ∧
    (∀ a x : EvenAlgebra,
      hestenesTomitaJ (cliffordLeftAction a (hestenesTomitaJ x)) =
        cliffordRightAction x (hestenesTomitaJ a)) ∧
    (∀ A X : StandardCarrier,
      matrixTomita (matrixLeftAction A (matrixTomita X)) =
        matrixRightAction X (matrixTomita A)) ∧
    (∀ d : ModularDatum, ∀ X : StandardCarrier,
      matrixTomita (d.delta (matrixTomita X)) = d.deltaInv X) := by
  exact ⟨hestenesAdjoint_is_standard_form_Tomita,
    hestenesTomitaJ_involutive,
    standard_form_left_right_exchange,
    matrix_standard_form_left_right_exchange,
    standard_form_modular_reversal⟩

end HestenesStandardFormModularArchitecture
end noncomputable section
