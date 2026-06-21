import Mathlib
import InfoGeometry.Algebra.QCCRSupergradingBridge
import InfoGeometry.Topology.DelaunayFlipInterfaces
import InfoGeometry.Topology.ThermodynamicGauge
import InfoGeometry.Topology.GrandUnificationLinker

/-!
# Super-Cuntz Dilation / Curvature Readout

Conservative finite interface for the slogan that a q-deformed super-Cuntz
boundary dilates spin-network edges and supplies a discrete curvature/deficit
readout.

This file does not construct a C*-algebra `O_{N|M}(q)`, a Hilbert-space modular
operator, Regge calculus, or a continuum curvature tensor.  It only records the
finite algebraic data already present in the q-CCR, Delaunay, and
thermodynamic-gauge owners, and proves readout lemmas from explicit hypotheses.

#### BUCKET 1: CLOSED FINITE THEOREMS

* q=0, q=-1, and q=1 read back to the existing Cuntz/CAR/CCR boundary lemmas;
* modular edge dilation is read from an explicit finite scaling field;
* Delaunay/Pachner matrix invariance is inherited from an explicitly supplied
  `DelaunayEquiv` owner;
* a supplied entropy-driven deficit equals `d_ln_Q` when the thermodynamic
  commutator comparison is supplied.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES

The curvature/deficit interpretation is conditional on
`IsEntropyDrivenDeficit`; no theorem derives that interpretation from geometry.

#### BUCKET 3: OPEN CLOSURE DEBT

Analytic super-Cuntz C*-algebras, true Regge deficit angles, positivity,
unitarity, and continuum gravitational curvature are outside this finite file.
-/

noncomputable section

namespace InfoGeometry.Topology.SuperCuntzDilationCurvature

open InfoGeometry.Algebra.QCCRSupergradingBridge
open InfoGeometry.Topology.ThermodynamicGauge

variable {N : ℕ} {Op : Type*} [Ring Op] [StarRing Op] [Algebra ℝ Op]

/--
Finite q-deformed super-Cuntz dilation packet.

`qccr` owns the q-dial algebraic relation.  `flow` owns the nonequilibrium
commutator.  The edge dilation and q-volume data are deliberately explicit
finite fields.
-/
structure SuperCuntzDilationPacket (N : ℕ) (Op : Type*)
    [Ring Op] [StarRing Op] [Algebra ℝ Op] where
  qccr : QCCRAlgebra N Op
  flow : CausalNonequilibriumFlow Op
  edge : Fin N → Op
  edgeEnergy : Fin N → ℝ
  modularStep : ℝ → Fin N → Op
  modular_dilates :
    ∀ t i, modularStep t i = (Real.exp (t * edgeEnergy i) : ℝ) • edge i
  volumeCell : Op
  volumeFlat : Op

/--
Explicit finite graded generator packet for the bosonic/fermionic boundary
split.  The grading is recorded as data; this file does not construct a
categorical super-algebra.
-/
structure GradedSuperCuntzPacket (N M : ℕ) (Op : Type*)
    [Ring Op] [StarRing Op] [Algebra ℝ Op] where
  q : ℝ
  bosonic : Fin N → Op
  fermionic : Fin M → Op
  bosonic_grade : Fin N → ZMod 2
  fermionic_grade : Fin M → ZMod 2
  bosonic_q_relation :
    ∀ i j, star (bosonic i) * bosonic j - q • (bosonic j * star (bosonic i)) =
      (if i = j then 1 else 0)
  fermionic_q_relation :
    ∀ i j, star (fermionic i) * fermionic j + q • (fermionic j * star (fermionic i)) =
      (if i = j then 1 else 0)
  cross_dilation : ℝ → Fin N → Op

/-- The bosonic q-relation is read out directly from the graded packet. -/
theorem bosonic_q_relation_readout
    (P : GradedSuperCuntzPacket N M Op) (i j : Fin N) :
    star (P.bosonic i) * P.bosonic j - P.q • (P.bosonic j * star (P.bosonic i)) =
      (if i = j then 1 else 0) :=
  P.bosonic_q_relation i j

/-- The fermionic q-relation is read out directly from the graded packet. -/
theorem fermionic_q_relation_readout
    (P : GradedSuperCuntzPacket N M Op) (i j : Fin M) :
    star (P.fermionic i) * P.fermionic j + P.q • (P.fermionic j * star (P.fermionic i)) =
      (if i = j then 1 else 0) :=
  P.fermionic_q_relation i j

/-- q-warped finite volume readout. -/
def qWarpedVolume (P : SuperCuntzDilationPacket N Op) : Op :=
  P.qccr.q • P.volumeCell

/-- q-deficit operator: q-warped finite volume minus the supplied flat volume. -/
def qDeficit (P : SuperCuntzDilationPacket N Op) : Op :=
  qWarpedVolume P - P.volumeFlat

/--
Explicit hypothesis that the q-deficit is driven by the thermodynamic entropy
production.  This is an external premise, not a theorem of this file.
-/
def IsEntropyDrivenDeficit (P : SuperCuntzDilationPacket N Op) : Prop :=
  qDeficit P = entropy_production P.flow

/-- q=0 recovers the Cuntz-isometry boundary already proved in the q-CCR owner. -/
theorem q_zero_cuntz_boundary
    (P : SuperCuntzDilationPacket N Op) (hq0 : P.qccr.q = 0) (i j : Fin N) :
    star (P.qccr.a i) * P.qccr.a j = (if i = j then 1 else 0) :=
  cuntz_apex_embedding P.qccr hq0 i j

/-- q=-1 recovers the fermionic anticommutator boundary. -/
theorem q_neg_one_fermionic_boundary
    (P : SuperCuntzDilationPacket N Op) (hqneg : P.qccr.q = -1) (i j : Fin N) :
    P.qccr.astar i * P.qccr.a j + P.qccr.a j * P.qccr.astar i =
      (if i = j then 1 else 0) :=
  q_neg_one_is_fermionic_anticommutator P.qccr hqneg i j

/-- q=1 recovers the bosonic commutator boundary. -/
theorem q_one_bosonic_boundary
    (P : SuperCuntzDilationPacket N Op) (hqpos : P.qccr.q = 1) (i j : Fin N) :
    P.qccr.astar i * P.qccr.a j - P.qccr.a j * P.qccr.astar i =
      (if i = j then 1 else 0) :=
  q_pos_one_is_bosonic_commutator P.qccr hqpos i j

/-- The supplied modular step acts as a finite edge dilation. -/
theorem modular_edge_dilation
    (P : SuperCuntzDilationPacket N Op) (t : ℝ) (i : Fin N) :
    P.modularStep t i = (Real.exp (t * P.edgeEnergy i) : ℝ) • P.edge i :=
  P.modular_dilates t i

/-- Definitional q-deficit expansion. -/
theorem qDeficit_eq_qWarped_sub_flat
    (P : SuperCuntzDilationPacket N Op) :
    qDeficit P = P.qccr.q • P.volumeCell - P.volumeFlat := by
  rfl

/-- At q=1, no volume gap remains if the supplied q-cell volume equals the flat one. -/
theorem qDeficit_zero_of_q_one_and_flat_volume
    (P : SuperCuntzDilationPacket N Op)
    (hq : P.qccr.q = 1)
    (hvol : P.volumeCell = P.volumeFlat) :
    qDeficit P = 0 := by
  simp [qDeficit, qWarpedVolume, hq, hvol]

/-- Read back the explicit entropy-driven deficit hypothesis. -/
theorem qDeficit_eq_entropy_of_drive
    (P : SuperCuntzDilationPacket N Op)
    (hdrive : IsEntropyDrivenDeficit P) :
    qDeficit P = entropy_production P.flow :=
  hdrive

/-- Entropy-driven q-deficit equals `d_ln_Q` once the flow commutator is supplied. -/
theorem qDeficit_eq_dlnQ_of_entropy_drive
    (P : SuperCuntzDilationPacket N Op)
    (hdrive : IsEntropyDrivenDeficit P)
    (hcomm :
      P.flow.P_forward * P.flow.P_backward -
          P.flow.P_backward * P.flow.P_forward =
        P.flow.d_ln_Q) :
    qDeficit P = P.flow.d_ln_Q := by
  rw [hdrive]
  exact de_rham_potential_equals_entropy_production_of_commutator P.flow hcomm

namespace DelaunayReadout

open InfoGeometry.Topology.Delaunay

/--
Finite packet combining an explicitly supplied Delaunay/Pachner equivalence with a
q-deformed dilation packet and explicit thermodynamic driving data.
-/
structure QWarpedDelaunayReadout (moving N : ℕ) (Op : Type*)
    [Ring Op] [StarRing Op] [Algebra ℝ Op] where
  before : DelaunayFlipWord moving
  after : DelaunayFlipWord moving
  packet : SuperCuntzDilationPacket N Op
  flip_equiv : DelaunayEquiv before after
  deficit_drive : IsEntropyDrivenDeficit packet
  flow_commutator :
    packet.flow.P_forward * packet.flow.P_backward -
        packet.flow.P_backward * packet.flow.P_forward =
      packet.flow.d_ln_Q

variable {moving : ℕ}

/--
Combined readout: the Delaunay matrix is invariant under the supplied flip
equivalence, and the supplied q-deficit reads as `d_ln_Q`.
-/
theorem q_warped_pachner_readout
    (R : QWarpedDelaunayReadout moving N Op) :
    rohozhkinMatrix R.before = rohozhkinMatrix R.after ∧
      qDeficit R.packet = R.packet.flow.d_ln_Q :=
  ⟨rohozhkinMatrix_respects_flip_word_equiv R.flip_equiv,
    qDeficit_eq_dlnQ_of_entropy_drive
      R.packet R.deficit_drive R.flow_commutator⟩

end DelaunayReadout

namespace GrandUnificationReadout

open InfoGeometry.Topology.GrandUnificationLinker

/--
Finite connector from a q-dilation packet to an existing GrandUnification jewel.
The shared-flow condition is explicit.
-/
structure QDilationJewel (N : ℕ) (Op : Type*)
    [Ring Op] [StarRing Op] [Algebra ℝ Op] where
  packet : SuperCuntzDilationPacket N Op
  jewel : QuantumJewel Op
  same_flow : jewel.thermodynamic_flow = packet.flow

/-- The jewel's DAG-volume preservation theorem is unchanged by carrying q-data. -/
theorem dag_volume_preserved_with_q_data
    (J : QDilationJewel N Op) :
    J.jewel.dag_edge * amplituhedron_volume_element J.jewel =
      amplituhedron_volume_element J.jewel * J.jewel.dag_edge :=
  global_isometry_preservation J.jewel

/--
If the jewel and q-dilation packet share the same thermodynamic flow, the
entropy readout transfers across the connector.
-/
theorem entropy_alignment_transfers_to_q_packet
    (J : QDilationJewel N Op)
    (hcomm :
      J.packet.flow.P_forward * J.packet.flow.P_backward -
          J.packet.flow.P_backward * J.packet.flow.P_forward =
        J.packet.flow.d_ln_Q) :
    entropy_production J.packet.flow = J.packet.flow.d_ln_Q := by
  exact de_rham_potential_equals_entropy_production_of_commutator
    J.packet.flow hcomm

end GrandUnificationReadout

end InfoGeometry.Topology.SuperCuntzDilationCurvature

end noncomputable section
