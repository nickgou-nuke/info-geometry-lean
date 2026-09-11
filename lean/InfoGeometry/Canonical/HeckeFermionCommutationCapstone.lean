import InfoGeometry.Quantum.HeckeFermionCommutation
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.HeckeFermionCommutationCapstone

open InfoGeometry.Quantum.HeckeFermionCommutation

theorem capstone_hecke_fermion_commutation_synthesis (p : ℕ) (f : ℕ → ℂ) (n : ℕ) :
    heckeOperator p (primeShiftOperator p f) n =
      primeShiftOperator p (heckeOperator p f) n := by
  exact hecke_prime_shift_commute p f n

end InfoGeometry.Canonical.HeckeFermionCommutationCapstone
