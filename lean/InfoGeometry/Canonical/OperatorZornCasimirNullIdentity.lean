import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# A theorem-safe operator-valued Zorn null identity

This owner records only the algebraic consequence of a chosen scalar
quadratic readout.  It does not identify that readout with a representation
theoretic Casimir, a Majorana mode, or an anyon sector.
-/

namespace InfoGeometry.Canonical

variable {A : Type*} [Ring A]

def operatorZornCasimir (Z : OperatorZornMatrix A) : A :=
  Z.n_plus * Z.n_minus - operatorDot Z.sigma_plus Z.sigma_minus

theorem operatorZornCasimir_zero_diagonal_implies_dot_zero
    (Z : OperatorZornMatrix A)
    (hcasimir : operatorZornCasimir Z = 0)
    (hplus : Z.n_plus = 0)
    (hminus : Z.n_minus = 0) :
    operatorDot Z.sigma_plus Z.sigma_minus = 0 := by
  have hdiag : Z.n_plus * Z.n_minus = 0 := by
    rw [hplus, hminus, zero_mul]
  unfold operatorZornCasimir at hcasimir
  rw [hdiag] at hcasimir
  exact neg_eq_zero.mp (by simpa using hcasimir)

end InfoGeometry.Canonical
