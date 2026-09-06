import InfoGeometry.Quantum.SuperchargeAlgebra

namespace InfoGeometry.Canonical.SuperchargeAlgebraCapstone

open InfoGeometry.Quantum.SuperchargeAlgebra

theorem capstone_supercharge_algebra_synthesis
    {R : Type*} [Ring R] (a_dag f : R) (E_0 : R)
    (hf : f * f = 0) (h_comm : f * a_dag = a_dag * f) :
    (NilpotentSquare (a_dag * f)) ∧
    (SuperHamiltonian 0 0 E_0 = E_0) :=
  grand_supercharge_algebra_synthesis a_dag f E_0 hf h_comm

end InfoGeometry.Canonical.SuperchargeAlgebraCapstone
