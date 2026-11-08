import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ThermodynamicGauge

namespace InfoGeometry.Topology.GrandUnificationLinker

/-!
# Grand Unification Linker

Conservative finite algebraic linker between split generators, a DAG-flow edge,
and the thermodynamic gauge readout.

#### BUCKET 1: CLOSED FINITE THEOREMS
The symmetric mixed element commutes with the DAG edge when both directed flow
compatibilities are explicit. A generic square-zero element annihilates its
symmetric-mixed-product sandwich. These are ring identities, not mass-shell or
scattering-residue statements.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
The entropy alignment theorem is conditional on an explicit commutator
comparison for the thermodynamic flow.

#### BUCKET 3: OPEN CLOSURE DEBT
No amplituhedron, Bost-Connes, Wilson-loop, or continuum scattering theorem is
derived in this finite algebraic file.
-/

variable {Op : Type*} [Ring Op]

/-- The symmetric mixed product of two elements in an associative ring. -/
def symmetric_mixed_element (a b : Op) : Op := a * b + b * a

/-- Entropy-production readout aligned to the log-affinity from an explicit
commutator comparison. -/
theorem entropy_alignment
    (flow : ThermodynamicGauge.CausalNonequilibriumFlow Op)
    (hcomm :
      flow.P_forward * flow.P_backward
        - flow.P_backward * flow.P_forward = flow.d_ln_Q) :
    ThermodynamicGauge.entropy_production flow = flow.d_ln_Q := by
  simpa using
    ThermodynamicGauge.de_rham_potential_equals_entropy_production_of_commutator
      (flow := flow) hcomm

/--
A Pachner flip whose commutator is coupled to entropy production is equivalently
coupled to the supplied de Rham logarithmic potential once the thermodynamic
commutator comparison is supplied.
-/
theorem pachner_flip_entropy_commutation
    (flow : ThermodynamicGauge.CausalNonequilibriumFlow Op)
    (T_flip : Op)
    (hcoupling :
      T_flip * flow.P_forward - flow.P_forward * T_flip =
        ThermodynamicGauge.entropy_production flow)
    (hcomm :
      flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward =
        flow.d_ln_Q) :
    T_flip * flow.P_forward - flow.P_forward * T_flip = flow.d_ln_Q := by
  rw [hcoupling]
  exact ThermodynamicGauge.de_rham_potential_equals_entropy_production_of_commutator
    (flow := flow) hcomm

/--
Detailed balance gives loop closure when the flat-limit commutation premise is
supplied explicitly.
-/
theorem loop_cross_commutation_closure
    (flow : ThermodynamicGauge.CausalNonequilibriumFlow Op)
    (T_flip loop_operator : Op)
    (hflat_commutes :
      flow.d_ln_Q = 0 → T_flip * loop_operator = loop_operator * T_flip)
    (hcomm :
      flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward =
        flow.d_ln_Q)
    (h_db : ThermodynamicGauge.entropy_production flow = 0) :
    T_flip * loop_operator = loop_operator * T_flip := by
  apply hflat_commutes
  have h_entropy_dln : ThermodynamicGauge.entropy_production flow = flow.d_ln_Q :=
    ThermodynamicGauge.de_rham_potential_equals_entropy_production_of_commutator
      (flow := flow) hcomm
  exact Eq.trans (Eq.symm h_entropy_dln) h_db

/-- Gauge covariance passes through the thermodynamic data. -/
theorem entropy_scale_covariance
    (flow : ThermodynamicGauge.CausalNonequilibriumFlow Op)
    [Algebra ℝ Op] (l : ℝ) (h_l : l ≠ 0) :
    (l • flow.P_forward) * flow.d_ln_Q * ((1 / l) • flow.P_backward) =
      ThermodynamicGauge.thermodynamic_gauge_connection flow := by
  simpa using
    ThermodynamicGauge.gauge_field_covariance
      (flow := flow) l h_l

/-- The two directed intertwining equations imply commutation with the
symmetric mixed product. -/
theorem dag_edge_commutes_with_symmetric_mixed
    (S_plus S_minus dag_edge : Op)
    (compat_plus : dag_edge * S_plus = S_minus * dag_edge)
    (compat_minus : dag_edge * S_minus = S_plus * dag_edge) :
    dag_edge * symmetric_mixed_element S_plus S_minus =
      symmetric_mixed_element S_plus S_minus * dag_edge := by
  calc
    dag_edge * symmetric_mixed_element S_plus S_minus
        = dag_edge * (S_plus * S_minus) + dag_edge * (S_minus * S_plus) := by
              rw [symmetric_mixed_element, mul_add]
    _ = (dag_edge * S_plus) * S_minus +
          (dag_edge * S_minus) * S_plus := by
          rw [mul_assoc, mul_assoc]
    _ = (S_minus * dag_edge) * S_minus +
          (S_plus * dag_edge) * S_plus := by
          rw [compat_plus, compat_minus]
    _ = S_minus * (dag_edge * S_minus) +
          S_plus * (dag_edge * S_plus) := by
          rw [← mul_assoc, ← mul_assoc]
    _ = S_minus * (S_plus * dag_edge) +
          S_plus * (S_minus * dag_edge) := by
          rw [compat_minus, compat_plus]
    _ = S_minus * S_plus * dag_edge + S_plus * S_minus * dag_edge := by
          rw [mul_assoc, mul_assoc]
    _ = S_plus * S_minus * dag_edge + S_minus * S_plus * dag_edge := by
          rw [add_comm]
    _ = symmetric_mixed_element S_plus S_minus * dag_edge := by
          rw [symmetric_mixed_element, add_mul]

/-- A square-zero element annihilates its sandwich with the symmetric mixed
product, in any associative ring. -/
theorem nilpotent_sandwich_zero (N X : Op) (hN : N * N = 0) :
    N * symmetric_mixed_element N X * N = 0 := by
  calc
    N * symmetric_mixed_element N X * N
        = (N * (N * X)) * N + (N * (X * N)) * N := by
          simp [symmetric_mixed_element, mul_add, add_mul]
    _ = 0 := by
          have hleft : N * (N * X) = 0 := by
            rw [← mul_assoc, hN, zero_mul]
          have hright : (N * (X * N)) * N = 0 := by
            calc
              (N * (X * N)) * N = N * (X * (N * N)) := by
                simp only [mul_assoc]
              _ = 0 := by simp [hN]
          rw [hleft, zero_mul, hright, add_zero]

end InfoGeometry.Topology.GrandUnificationLinker
