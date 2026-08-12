import InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra
import InfoGeometry.Optics.OperatorCausalSoldering
import InfoGeometry.Optics.AbelianOperatorValuedConnection
import InfoGeometry.Optics.JonesPoincareSphere

/-!
# Chiral four-vector operator synthesis

This is a consolidation owner for the finite, already existing layers.  It
records the Pauli commutator channel, faithful operator-valued soldering,
Lorentz determinant preservation, the Jones null readout, and the Abelian
curvature reduction.  It does not assert a carrier equivalence between Jones
matrices and split-octonionic operators.
-/

noncomputable section

namespace InfoGeometry.Physics.ChiralFourVectorOperatorSynthesis

open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra
open InfoGeometry.Physics.LorentzChiralCuntzBridge
open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Optics.OperatorValuedCliffordJones
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Optics.JonesPoincareSphere

def matrixCommutator (A B : M2C) : M2C := A * B - B * A

theorem pauli_commutator_sigma1_sigma2 :
    matrixCommutator σ1 σ2 = (2 * Complex.I) • σ3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixCommutator, σ1, σ2, σ3, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf <;>
      norm_num [Complex.I_mul_I, Complex.I_sq]

theorem pauli_commutator_sigma2_sigma3 :
    matrixCommutator σ2 σ3 = (2 * Complex.I) • σ1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixCommutator, σ1, σ2, σ3, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf <;>
      norm_num [Complex.I_mul_I, Complex.I_sq]

theorem pauli_commutator_sigma3_sigma1 :
    matrixCommutator σ3 σ1 = (2 * Complex.I) • σ2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixCommutator, σ1, σ2, σ3, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf <;>
      norm_num [Complex.I_mul_I, Complex.I_sq]

theorem pauli_antisymmetric_channel :
    matrixCommutator σ1 σ2 = (2 * Complex.I) • σ3 ∧
      matrixCommutator σ2 σ3 = (2 * Complex.I) • σ1 ∧
        matrixCommutator σ3 σ1 = (2 * Complex.I) • σ2 :=
  ⟨pauli_commutator_sigma1_sigma2, pauli_commutator_sigma2_sigma3,
    pauli_commutator_sigma3_sigma1⟩

theorem operator_four_vector_soldering_faithful
    {W : Type*} [AddCommGroup W] [Module ℂ W] :
    Function.Injective (operatorSolderingAction (W := W)) :=
  operatorSolderingAction_injective

theorem operator_four_vector_zero_detected
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (v : OperatorFourVector W) :
    operatorSolderingAction v = 0 ↔ v = 0 :=
  operatorSolderingAction_eq_zero_iff v

/-- The operator-valued four-vector reaches the circular/Weyl packet through
    the existing causal reconstruction.  The coordinate order is
    `(scalar, chiral, exchange, circular) = (v 0, v 3, v 1, v 2)`; no Zorn or
    Clifford identification is asserted here. -/
theorem operator_four_vector_soldering_circular_basis
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (v : OperatorFourVector W) :
    operatorSoldering v =
      v 0 • (sheetIdentity : SheetMatrix (EndW W)) +
      v 3 • (sheetGamma : SheetMatrix (EndW W)) +
      v 1 • (sheetJ : SheetMatrix (EndW W)) +
      v 2 • (sheetCircular : SheetMatrix (EndW W)) := by
  change reconstructOperator (causalCoordinatesOfFourVector v) = _
  exact reconstructOperator_eq_packet (causalCoordinatesOfFourVector v)

theorem pauli_four_vector_lorentz_readout
    (g : SL2C) (P : FourMomentum) :
    pauliMomentum (spinLorentzAction g P) =
        chiralConjAct g (pauliMomentum P) ∧
      minkowskiSq (spinLorentzAction g P) = minkowskiSq P :=
  ⟨pauliMomentum_spinLorentzAction g P,
    spinLorentzAction_preserves_minkowskiSq g P⟩

theorem stokes_four_vector_is_null (J : JonesSpinor) :
    (JonesSpinor.stokesMinkowski4 J).q = 0 :=
  JonesSpinor.stokesMinkowski4_q J

theorem abelian_connection_is_derivative
    {Point Tangent Value : Type*} [Ring Value]
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := Value))
    (hAbelian : IsAbelianForm C.form) (p : Point) (X Y : Tangent) :
    curvature C p X Y = C.derivative p X Y :=
  curvature_eq_derivative_of_abelian C hAbelian p X Y

theorem finite_chiral_four_vector_synthesis
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (g : SL2C) (P : FourMomentum) (J : JonesSpinor)
    (v : OperatorFourVector W) :
    matrixCommutator σ1 σ2 = (2 * Complex.I) • σ3 ∧
      pauliMomentum (spinLorentzAction g P) =
        chiralConjAct g (pauliMomentum P) ∧
      minkowskiSq (spinLorentzAction g P) = minkowskiSq P ∧
      (JonesSpinor.stokesMinkowski4 J).q = 0 ∧
      (operatorSolderingAction v = 0 ↔ v = 0) := by
  exact ⟨pauli_commutator_sigma1_sigma2,
    pauliMomentum_spinLorentzAction g P,
    spinLorentzAction_preserves_minkowskiSq g P,
    JonesSpinor.stokesMinkowski4_q J,
    operatorSolderingAction_eq_zero_iff v⟩

end InfoGeometry.Physics.ChiralFourVectorOperatorSynthesis
