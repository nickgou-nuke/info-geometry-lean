/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.SuperchargeAlgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.SuperchargeAlgebraCapstone

open InfoGeometry.Quantum.SuperchargeAlgebra

/-- Canonical synthesis of square-zero supercharge and vacuum-energy laws. -/
theorem capstone_supercharge_algebra_synthesis
    {R : Type*} [Ring R] (a_dag f : R) (E_0 : R)
    (hf : f * f = 0) (h_comm : f * a_dag = a_dag * f) :
    (NilpotentSquare (a_dag * f)) ∧
    (SuperHamiltonian 0 0 E_0 = E_0) := by
  exact ⟨supercharge_nilpotent_of_square_zero a_dag f hf h_comm,
    super_hamiltonian_vacuum_energy E_0⟩

end InfoGeometry.Canonical.SuperchargeAlgebraCapstone
