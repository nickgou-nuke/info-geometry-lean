import Mathlib
import InfoGeometry.Topology.DelaunayFlipInterfaces
import InfoGeometry.Topology.ThermodynamicGauge

namespace InfoGeometry.Topology.GrandUnificationLinker

/-!
# Grand Unification Linker

Conservative finite algebraic linker between split generators, a DAG-flow edge,
and the thermodynamic gauge readout.

#### BUCKET 1: CLOSED FINITE THEOREMS
The symmetric mixed element commutes with the DAG edge when both directed flow
compatibilities are explicit. The left and right nilpotent boundary channels
collapse under the stated square-zero hypotheses.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
The entropy alignment theorem is conditional on an explicit commutator
comparison for the thermodynamic flow.

#### BUCKET 3: OPEN CLOSURE DEBT
No amplituhedron, Bost-Connes, Wilson-loop, or continuum scattering theorem is
derived in this finite algebraic file.
-/

structure QuantumJewel (Op : Type*) [Ring Op] [Star Op] where
  S_plus : Op
  S_minus : Op
  isometry_plus : star S_plus * S_plus = 1
  isometry_minus : star S_minus * S_minus = 1
  klein_quadric_plus : S_plus * S_plus = 0
  klein_quadric_minus : S_minus * S_minus = 0
  dag_edge : Op
  thermodynamic_flow : ThermodynamicGauge.CausalNonequilibriumFlow Op
  compat_flow_plus : dag_edge * S_plus = S_minus * dag_edge
  compat_flow_minus : dag_edge * S_minus = S_plus * dag_edge

variable {Op : Type*} [Ring Op]

/-- The conservative mixed volume element in this algebraic window. -/
def amplituhedron_volume_element [Star Op] (jewel : QuantumJewel Op) : Op :=
  jewel.S_plus * jewel.S_minus + jewel.S_minus * jewel.S_plus

/-- Entropy-production readout aligned to the log-affinity from an explicit
commutator comparison. -/
theorem entropy_alignment
    [Star Op]
    (jewel : QuantumJewel Op)
    (hcomm :
      jewel.thermodynamic_flow.P_forward * jewel.thermodynamic_flow.P_backward
        - jewel.thermodynamic_flow.P_backward * jewel.thermodynamic_flow.P_forward =
          jewel.thermodynamic_flow.d_ln_Q) :
    ThermodynamicGauge.entropy_production jewel.thermodynamic_flow =
      jewel.thermodynamic_flow.d_ln_Q := by
  simpa using
    ThermodynamicGauge.de_rham_potential_equals_entropy_production_of_commutator
      (flow := jewel.thermodynamic_flow) hcomm

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
    [Star Op]
    (jewel : QuantumJewel Op) [Algebra ℝ Op] (l : ℝ) (h_l : l ≠ 0) :
    (l • jewel.thermodynamic_flow.P_forward) * jewel.thermodynamic_flow.d_ln_Q
      * ((1 / l) • jewel.thermodynamic_flow.P_backward) =
      ThermodynamicGauge.thermodynamic_gauge_connection jewel.thermodynamic_flow := by
  simpa using
    ThermodynamicGauge.gauge_field_covariance
      (flow := jewel.thermodynamic_flow) l h_l

/-- DAG flow compatibility preserves the symmetric mixed volume element. -/
theorem global_isometry_preservation
    [Star Op]
    (jewel : QuantumJewel Op) :
    jewel.dag_edge * amplituhedron_volume_element jewel =
      amplituhedron_volume_element jewel * jewel.dag_edge := by
  calc
    jewel.dag_edge * amplituhedron_volume_element jewel
        = jewel.dag_edge * (jewel.S_plus * jewel.S_minus)
            + jewel.dag_edge * (jewel.S_minus * jewel.S_plus) := by
              rw [amplituhedron_volume_element, mul_add]
    _ = (jewel.dag_edge * jewel.S_plus) * jewel.S_minus +
          (jewel.dag_edge * jewel.S_minus) * jewel.S_plus := by
          rw [mul_assoc, mul_assoc]
    _ = (jewel.S_minus * jewel.dag_edge) * jewel.S_minus +
          (jewel.S_plus * jewel.dag_edge) * jewel.S_plus := by
          rw [jewel.compat_flow_plus, jewel.compat_flow_minus]
    _ = jewel.S_minus * (jewel.dag_edge * jewel.S_minus) +
          jewel.S_plus * (jewel.dag_edge * jewel.S_plus) := by
          rw [← mul_assoc, ← mul_assoc]
    _ = jewel.S_minus * (jewel.S_plus * jewel.dag_edge) +
          jewel.S_plus * (jewel.S_minus * jewel.dag_edge) := by
          rw [jewel.compat_flow_minus, jewel.compat_flow_plus]
    _ = jewel.S_minus * jewel.S_plus * jewel.dag_edge +
          jewel.S_plus * jewel.S_minus * jewel.dag_edge := by
          rw [mul_assoc, mul_assoc]
    _ = jewel.S_plus * jewel.S_minus * jewel.dag_edge +
          jewel.S_minus * jewel.S_plus * jewel.dag_edge := by
          rw [add_comm]
    _ = (jewel.S_plus * jewel.S_minus + jewel.S_minus * jewel.S_plus) * jewel.dag_edge := by
          rw [add_mul, mul_assoc]

/-- On-shell collapse under `S_plus^2 = 0`. -/
theorem on_shell_boundary_collapse
    [Star Op]
    (jewel : QuantumJewel Op) :
    jewel.S_plus * amplituhedron_volume_element jewel * jewel.S_plus = 0 := by
  calc
    jewel.S_plus * amplituhedron_volume_element jewel * jewel.S_plus
      = (jewel.S_plus * (jewel.S_plus * jewel.S_minus + jewel.S_minus * jewel.S_plus)) * jewel.S_plus := by
          rw [amplituhedron_volume_element, mul_assoc]
    _ = (jewel.S_plus * (jewel.S_plus * jewel.S_minus)
          + jewel.S_plus * (jewel.S_minus * jewel.S_plus)) * jewel.S_plus := by
          rw [mul_add]
    _ = (jewel.S_plus * (jewel.S_plus * jewel.S_minus)) * jewel.S_plus +
          (jewel.S_plus * (jewel.S_minus * jewel.S_plus)) * jewel.S_plus := by
          rw [add_mul]
    _ = jewel.S_plus * jewel.S_plus * jewel.S_minus * jewel.S_plus
          + jewel.S_plus * jewel.S_minus * jewel.S_plus * jewel.S_plus := by
          simp [mul_assoc]
    _ = 0 := by
          have hp1 : jewel.S_plus * jewel.S_plus * jewel.S_minus * jewel.S_plus = 0 := by
            rw [mul_assoc]
            rw [jewel.klein_quadric_plus]
            simp
          have hp2 : jewel.S_plus * jewel.S_minus * jewel.S_plus * jewel.S_plus = 0 := by
            rw [mul_assoc]
            rw [jewel.klein_quadric_plus]
            simp
          rw [hp1, hp2]
          simp

/-- On-shell collapse under `S_minus^2 = 0`. -/
theorem on_shell_boundary_collapse_minus
    [Star Op]
    (jewel : QuantumJewel Op) :
    jewel.S_minus * amplituhedron_volume_element jewel * jewel.S_minus = 0 := by
  calc
    jewel.S_minus * amplituhedron_volume_element jewel * jewel.S_minus
      = (jewel.S_minus * (jewel.S_plus * jewel.S_minus + jewel.S_minus * jewel.S_plus)) * jewel.S_minus := by
          rw [amplituhedron_volume_element, mul_assoc]
    _ = (jewel.S_minus * (jewel.S_plus * jewel.S_minus)
          + jewel.S_minus * (jewel.S_minus * jewel.S_plus)) * jewel.S_minus := by
          rw [mul_add]
    _ = (jewel.S_minus * (jewel.S_plus * jewel.S_minus)) * jewel.S_minus +
          (jewel.S_minus * (jewel.S_minus * jewel.S_plus)) * jewel.S_minus := by
          rw [add_mul]
    _ = jewel.S_minus * jewel.S_plus * jewel.S_minus * jewel.S_minus
          + jewel.S_minus * jewel.S_minus * jewel.S_plus * jewel.S_minus := by
          simp [mul_assoc]
    _ = 0 := by
          have hm1 : jewel.S_minus * jewel.S_plus * jewel.S_minus * jewel.S_minus = 0 := by
            rw [mul_assoc]
            rw [jewel.klein_quadric_minus]
            simp
          have hm2 : jewel.S_minus * jewel.S_minus * jewel.S_plus * jewel.S_minus = 0 := by
            rw [mul_assoc]
            rw [jewel.klein_quadric_minus]
            simp
          rw [hm1, hm2]
          simp

/-- Both nilpotent boundary channels collapse. -/
theorem on_shell_boundary_collapse_pair
    [Star Op]
    (jewel : QuantumJewel Op) :
    jewel.S_plus * amplituhedron_volume_element jewel * jewel.S_plus = 0 ∧
      jewel.S_minus * amplituhedron_volume_element jewel * jewel.S_minus = 0 :=
  ⟨on_shell_boundary_collapse jewel, on_shell_boundary_collapse_minus jewel⟩

variable {n : ℕ}

/-- An explicitly supplied Delaunay/Pachner flip equivalence preserves the Rohozhkin matrix. -/
theorem rohozhkin_matrix_invariant
    (before after : InfoGeometry.Topology.Delaunay.DelaunayFlipWord n)
    (flip_equiv : InfoGeometry.Topology.Delaunay.DelaunayEquiv before after) :
    InfoGeometry.Topology.Delaunay.rohozhkinMatrix before =
      InfoGeometry.Topology.Delaunay.rohozhkinMatrix after :=
  InfoGeometry.Topology.Delaunay.rohozhkinMatrix_respects_flip_word_equiv
    flip_equiv

/-- The closed DAG-flow volume preservation theorem for a supplied jewel. -/
theorem dag_volume_preserved
    [Star Op]
    (jewel : QuantumJewel Op) :
    jewel.dag_edge * amplituhedron_volume_element jewel =
      amplituhedron_volume_element jewel * jewel.dag_edge :=
  global_isometry_preservation jewel

/--
Combined finite readout: the Delaunay matrix invariant and the linker volume
invariant hold together for explicit supplied data.
-/
theorem pachner_linker_readout
    [Star Op]
    (before after : InfoGeometry.Topology.Delaunay.DelaunayFlipWord n)
    (flip_equiv : InfoGeometry.Topology.Delaunay.DelaunayEquiv before after)
    (jewel : QuantumJewel Op) :
    InfoGeometry.Topology.Delaunay.rohozhkinMatrix before =
        InfoGeometry.Topology.Delaunay.rohozhkinMatrix after ∧
      jewel.dag_edge * amplituhedron_volume_element jewel =
        amplituhedron_volume_element jewel * jewel.dag_edge :=
  ⟨rohozhkin_matrix_invariant before after flip_equiv, dag_volume_preserved jewel⟩

/--
Conditional thermodynamic readout alongside an explicitly supplied Delaunay/Pachner
equivalence.

The equality with `d_ln_Q` is not derived from Delaunay geometry here; it is
read back from the explicit commutator comparison supplied for the jewel's
thermodynamic flow.  The flip equivalence is included so this theorem has the
same finite owner surface as the Pachner readout, without hiding it in a packet.
-/
theorem entropy_production_eq_dlnQ
    [Star Op]
    (before after : InfoGeometry.Topology.Delaunay.DelaunayFlipWord n)
    (_flip_equiv : InfoGeometry.Topology.Delaunay.DelaunayEquiv before after)
    (jewel : QuantumJewel Op)
    (hcomm :
      jewel.thermodynamic_flow.P_forward *
          jewel.thermodynamic_flow.P_backward -
        jewel.thermodynamic_flow.P_backward *
          jewel.thermodynamic_flow.P_forward =
        jewel.thermodynamic_flow.d_ln_Q) :
    ThermodynamicGauge.entropy_production jewel.thermodynamic_flow =
      jewel.thermodynamic_flow.d_ln_Q :=
  entropy_alignment jewel hcomm

end InfoGeometry.Topology.GrandUnificationLinker
