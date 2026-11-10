import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

namespace InfoGeometry.Quantum.SuperPoincareCasimir

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {R : Type*} [Ring R]

def commutator (A B : R) : R :=
  A * B - B * A

def anticommutator (A B : R) : R :=
  A * B + B * A

def superPoincareCasimir (P_u P_v : R) : R :=
  4 * P_u * P_v

theorem casimir_commutator_Pu_noncomm (P_u P_v : R) :
    commutator (superPoincareCasimir P_u P_v) P_u = 4 * P_u * commutator P_v P_u := by
  unfold commutator superPoincareCasimir
  noncomm_ring

theorem casimir_commutator_Pv_noncomm (P_u P_v : R) :
    commutator (superPoincareCasimir P_u P_v) P_v = 4 * commutator P_u P_v * P_v := by
  unfold commutator superPoincareCasimir
  noncomm_ring

theorem casimir_commutes_with_Pu_of_comm (P_u P_v : R) (h_comm : P_v * P_u = P_u * P_v) :
    commutator (superPoincareCasimir P_u P_v) P_u = 0 := by
  rw [casimir_commutator_Pu_noncomm]
  unfold commutator
  rw [h_comm, sub_self, mul_zero]

theorem casimir_commutes_with_Pv_of_comm (P_u P_v : R) (h_comm : P_u * P_v = P_v * P_u) :
    commutator (superPoincareCasimir P_u P_v) P_v = 0 := by
  rw [casimir_commutator_Pv_noncomm]
  unfold commutator
  rw [h_comm, sub_self, mul_zero, zero_mul]

theorem casimir_commutes_with_Pu (P_u P_v : R) (h_comm : P_u * P_v = P_v * P_u) :
    commutator (superPoincareCasimir P_u P_v) P_u = 0 :=
  casimir_commutes_with_Pu_of_comm P_u P_v h_comm.symm

theorem casimir_commutes_with_Pv (P_u P_v : R) (h_comm : P_u * P_v = P_v * P_u) :
    commutator (superPoincareCasimir P_u P_v) P_v = 0 :=
  casimir_commutes_with_Pv_of_comm P_u P_v h_comm

end InfoGeometry.Quantum.SuperPoincareCasimir
