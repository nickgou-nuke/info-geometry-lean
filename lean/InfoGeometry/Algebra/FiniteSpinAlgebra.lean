import Mathlib.LinearAlgebra.Matrix.Basic

namespace InfoGeometry.Algebra.FiniteSpin

/-- Structure defining the finite SU(2) spin-1/2 algebra generation. -/
structure SpinHalfBasis (n : ℕ) where
  J_zero : Matrix (Fin n) (Fin n) ℂ
  J_plus : Matrix (Fin n) (Fin n) ℂ
  J_minus: Matrix (Fin n) (Fin n) ℂ

  -- Standard SU(2) ladder commutation relations
  h_commutator_z_plus  : J_zero * J_plus - J_plus * J_zero = J_plus
  h_commutator_z_minus : J_zero * J_minus - J_minus * J_zero = -J_minus
  h_commutator_plus_minus : J_plus * J_minus - J_minus * J_plus = 2 * J_zero

variable {n : ℕ} (basis : SpinHalfBasis n)

theorem spin_z_plus_commutation :
    basis.J_zero * basis.J_plus - basis.J_plus * basis.J_zero = basis.J_plus := by
  exact basis.h_commutator_z_plus

end InfoGeometry.Algebra.FiniteSpin
