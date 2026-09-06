import InfoGeometry.Algebra.CuntzLorentzPoincarePresentation
import InfoGeometry.Quantum.PoincareSupercharge

/-!
# Finite Cuntz/Poincare/Lorentz supercharge packet

This module connects the already-proved finite Cuntz super-Poincare packet with
Pauli/Hestenes supercharge readout and exact determinant-preserving Lorentz
transport.

The content is deliberately finite and algebraic:

* the Cuntz packet gives an odd supercharge with `{Q,Q}=2P`;
* the Pauli supercharge anticommutator matrix has determinant `4 P²` and trace
  readout recovering four-momentum;
* the exact finite Lorentz transport preserves the Pauli determinant, hence the
  Minkowski norm readout.
-/

noncomputable section

namespace InfoGeometry.Quantum.CuntzPoincareLorentzSupercharge

open Matrix
open InfoGeometry.Algebra.SupergradedSUSY
open InfoGeometry.Algebra.LorentzBiquaternionEquivalence
open InfoGeometry.Algebra.CuntzLorentzPoincarePresentation
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Quantum.PoincareSupercharge

/-- Pauli paravector matrix is the same finite Hermitian spacetime matrix. -/
theorem pauliMatrix_eq_hermitianSpacetimePoint (P : PauliParavector) :
    P.pauliMatrix = hermitianSpacetimePoint (P.energy : ℂ) (P.px : ℂ) (P.py : ℂ) (P.pz : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PauliParavector.pauliMatrix, hermitianSpacetimePoint,
      InfoGeometry.Physics.MD001MatrixQuantumGeometry.pauliSpacetimeMatrix,
      UnifiedMatrixBasis.I₂, UnifiedMatrixBasis.σ₁,
      UnifiedMatrixBasis.σ₂, UnifiedMatrixBasis.σ₃]
  all_goals ring

/-- Exact boost preserves determinant of a Pauli paravector matrix. -/
theorem exactBoostTransport_preserves_pauli_det (P : PauliParavector) :
    Matrix.det (exactBoostTransport P.pauliMatrix) = Matrix.det P.pauliMatrix := by
  exact exactBoostTransport_det P.pauliMatrix

/-- Twice-composed exact boost preserves determinant of a Pauli paravector matrix. -/
theorem exactBoostTransport_comp_self_preserves_pauli_det (P : PauliParavector) :
    Matrix.det (exactBoostTransport (exactBoostTransport P.pauliMatrix)) = Matrix.det P.pauliMatrix := by
  rw [exactBoostTransport_det]
  exact exactBoostTransport_det P.pauliMatrix

/-- Twice-composed exact boost preserves the Pauli Minkowski norm readout. -/
theorem exactBoostTransport_comp_self_pauli_minkowski (P : PauliParavector) :
    Matrix.det (exactBoostTransport (exactBoostTransport P.pauliMatrix)) = (P.minkowskiNormSq : ℂ) := by
  rw [exactBoostTransport_comp_self_preserves_pauli_det]
  exact PauliParavector.det_pauliMatrix_eq_minkowskiNormSq P

end InfoGeometry.Quantum.CuntzPoincareLorentzSupercharge

end noncomputable section
