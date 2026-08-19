import Mathlib.Tactic
import InfoGeometry.Topology.GrandUnificationLinker

/-!
# Grand Unification Colimit Transport

Finite-stage-to-limit transport for the topology linker corridor.

This file is deliberately conservative.  It does not construct the analytic
or categorical colimit of the Delaunay/Penrose spaces.  It proves that the
ring-level identities already owned by `GrandUnificationLinker` survive after
applying an explicit structure map `Stage →+* Limit`.

#### BUCKET 1: CLOSED FINITE THEOREMS

* entropy commutator readouts transport through any ring homomorphism;
* Pachner/thermodynamic commutator readouts transport through any ring
  homomorphism;
* the DAG mixed-volume preservation and nilpotent boundary-collapse theorems
  transport through any ring homomorphism;
* Rohozhkin/Delaunay invariance is available uniformly for every finite `n`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES

All limit statements depend on an explicit map `Stage →+* Limit`.  The loop
closure theorem also depends on the same explicit flat-commutation premise as
the finite-stage theorem.

#### BUCKET 3: OPEN CLOSURE DEBT

A genuine Delaunay/Penrose inductive colimit requires explicit bonding maps
`DelaunayFlipWord n → DelaunayFlipWord (n+1)` and compatibility theorems for
`DelaunayEquiv` and `rohozhkinMatrix`.  Those maps are not exposed by the
current Delaunay owner, so this file records only the uniform finite-stage
family for that branch.
-/

namespace InfoGeometry.Topology.GrandUnificationColimitTransport

open InfoGeometry.Topology

variable {Stage Limit : Type*} [Ring Stage] [Ring Limit]

/-- Push a finite thermodynamic flow through a ring homomorphism into a limit algebra. -/
def mapFlow (toLimit : Stage →+* Limit)
    (flow : ThermodynamicGauge.CausalNonequilibriumFlow Stage) :
    ThermodynamicGauge.CausalNonequilibriumFlow Limit where
  Q := toLimit flow.Q
  d_ln_Q := toLimit flow.d_ln_Q
  P_forward := toLimit flow.P_forward
  P_backward := toLimit flow.P_backward

/-- Mapping a finite flow along the identity ring homomorphism changes nothing. -/
theorem mapFlow_id
    (flow : ThermodynamicGauge.CausalNonequilibriumFlow Stage) :
    mapFlow (RingHom.id Stage) flow = flow := by
  rfl

/-- Mapping a finite flow along composed ring homomorphisms is functorial. -/
theorem mapFlow_comp
    {Target : Type*} [Ring Target]
    (toLimit : Stage →+* Limit) (toTarget : Limit →+* Target)
    (flow : ThermodynamicGauge.CausalNonequilibriumFlow Stage) :
    mapFlow toTarget (mapFlow toLimit flow) =
      mapFlow (toTarget.comp toLimit) flow := by
  rfl

/-- The entropy commutator comparison transports into the supplied limit algebra. -/
theorem map_entropy_commutator_to_limit
    (toLimit : Stage →+* Limit)
    (flow : ThermodynamicGauge.CausalNonequilibriumFlow Stage)
    (hcomm :
      flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward =
        flow.d_ln_Q) :
    (mapFlow toLimit flow).P_forward * (mapFlow toLimit flow).P_backward -
        (mapFlow toLimit flow).P_backward * (mapFlow toLimit flow).P_forward =
      (mapFlow toLimit flow).d_ln_Q := by
  change toLimit flow.P_forward * toLimit flow.P_backward -
        toLimit flow.P_backward * toLimit flow.P_forward =
      toLimit flow.d_ln_Q
  rw [← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_sub, hcomm]

/-- Entropy alignment survives after applying the limit structure map. -/
theorem map_entropy_alignment_to_limit
    (toLimit : Stage →+* Limit)
    (flow : ThermodynamicGauge.CausalNonequilibriumFlow Stage)
    (hcomm :
      flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward =
        flow.d_ln_Q) :
    ThermodynamicGauge.entropy_production (mapFlow toLimit flow) =
      (mapFlow toLimit flow).d_ln_Q :=
  ThermodynamicGauge.de_rham_potential_equals_entropy_production_of_commutator
    (flow := mapFlow toLimit flow)
    (map_entropy_commutator_to_limit toLimit flow hcomm)

/--
The finite Pachner/thermodynamic commutator readout transports into the supplied
limit algebra.
-/
theorem map_pachner_flip_entropy_commutation_to_limit
    (toLimit : Stage →+* Limit)
    (flow : ThermodynamicGauge.CausalNonequilibriumFlow Stage)
    (T_flip : Stage)
    (hcoupling :
      T_flip * flow.P_forward - flow.P_forward * T_flip =
        ThermodynamicGauge.entropy_production flow)
    (hcomm :
      flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward =
        flow.d_ln_Q) :
    toLimit T_flip * (mapFlow toLimit flow).P_forward -
        (mapFlow toLimit flow).P_forward * toLimit T_flip =
      (mapFlow toLimit flow).d_ln_Q := by
  have hstage :
      T_flip * flow.P_forward - flow.P_forward * T_flip = flow.d_ln_Q :=
    GrandUnificationLinker.pachner_flip_entropy_commutation flow T_flip hcoupling hcomm
  change toLimit T_flip * toLimit flow.P_forward -
        toLimit flow.P_forward * toLimit T_flip =
      toLimit flow.d_ln_Q
  rw [← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_sub, hstage]

/--
The detailed-balance loop closure transports into the supplied limit algebra.
The flat-commutation premise remains explicit at the finite stage.
-/
theorem map_loop_cross_commutation_closure_to_limit
    (toLimit : Stage →+* Limit)
    (flow : ThermodynamicGauge.CausalNonequilibriumFlow Stage)
    (T_flip loopOperator : Stage)
    (hflat_commutes :
      flow.d_ln_Q = 0 → T_flip * loopOperator = loopOperator * T_flip)
    (hcomm :
      flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward =
        flow.d_ln_Q)
    (hdb : ThermodynamicGauge.entropy_production flow = 0) :
    toLimit T_flip * toLimit loopOperator =
      toLimit loopOperator * toLimit T_flip := by
  have hstage :
      T_flip * loopOperator = loopOperator * T_flip :=
    GrandUnificationLinker.loop_cross_commutation_closure
      flow T_flip loopOperator hflat_commutes hcomm hdb
  rw [← RingHom.map_mul, ← RingHom.map_mul, hstage]

/-- The DAG mixed-volume preservation theorem transports into the supplied limit algebra. -/
theorem map_global_isometry_preservation_to_limit
    [Star Stage]
    (toLimit : Stage →+* Limit)
    (jewel : GrandUnificationLinker.QuantumJewel Stage) :
    toLimit jewel.dag_edge *
        (toLimit jewel.S_plus * toLimit jewel.S_minus +
          toLimit jewel.S_minus * toLimit jewel.S_plus) =
      (toLimit jewel.S_plus * toLimit jewel.S_minus +
          toLimit jewel.S_minus * toLimit jewel.S_plus) *
        toLimit jewel.dag_edge := by
  have h := congrArg toLimit (GrandUnificationLinker.global_isometry_preservation jewel)
  simpa [GrandUnificationLinker.amplituhedron_volume_element] using h

/-- The plus nilpotent boundary collapse transports into the supplied limit algebra. -/
theorem map_on_shell_boundary_collapse_to_limit
    [Star Stage]
    (toLimit : Stage →+* Limit)
    (jewel : GrandUnificationLinker.QuantumJewel Stage) :
    toLimit jewel.S_plus *
        (toLimit jewel.S_plus * toLimit jewel.S_minus +
          toLimit jewel.S_minus * toLimit jewel.S_plus) *
      toLimit jewel.S_plus =
      0 := by
  have h := congrArg toLimit (GrandUnificationLinker.on_shell_boundary_collapse jewel)
  simpa [GrandUnificationLinker.amplituhedron_volume_element] using h

/-- The minus nilpotent boundary collapse transports into the supplied limit algebra. -/
theorem map_on_shell_boundary_collapse_minus_to_limit
    [Star Stage]
    (toLimit : Stage →+* Limit)
    (jewel : GrandUnificationLinker.QuantumJewel Stage) :
    toLimit jewel.S_minus *
        (toLimit jewel.S_plus * toLimit jewel.S_minus +
          toLimit jewel.S_minus * toLimit jewel.S_plus) *
      toLimit jewel.S_minus =
      0 := by
  have h := congrArg toLimit (GrandUnificationLinker.on_shell_boundary_collapse_minus jewel)
  simpa [GrandUnificationLinker.amplituhedron_volume_element] using h

/--
Uniform finite-stage Delaunay/Rohozhkin invariance.

This is the current honest endpoint for the `n`-dependent Delaunay theorem:
the invariant is available at every finite `n`.  A true Delaunay colimit theorem
requires bonding maps between the finite word types.
-/
theorem delaunay_rohozhkin_invariant_all_finite_stages :
    ∀ (n : ℕ) (before after : Delaunay.DelaunayFlipWord n),
      Delaunay.DelaunayEquiv before after →
        Delaunay.rohozhkinMatrix before = Delaunay.rohozhkinMatrix after := by
  intro n before after h
  exact GrandUnificationLinker.rohozhkin_matrix_invariant before after h

/-- A supplied bonding map has the supplied colimit image. -/
theorem delaunay_bond_to_supplied_colimit
    {LimitD : Type*}
    (bond : ∀ n : ℕ,
      Delaunay.DelaunayFlipWord n → Delaunay.DelaunayFlipWord (n + 1))
    (toLimit : ∀ n : ℕ, Delaunay.DelaunayFlipWord n → LimitD)
    (cone_comm :
      ∀ (n : ℕ) (W : Delaunay.DelaunayFlipWord n),
        toLimit (n + 1) (bond n W) = toLimit n W)
    (n : ℕ) (W : Delaunay.DelaunayFlipWord n) :
    toLimit (n + 1) (bond n W) = toLimit n W :=
  cone_comm n W

/--
A finite Delaunay/Pachner equivalence survives in a supplied colimit cone when
the cone is explicitly assumed to respect finite-stage equivalence.
-/
theorem delaunay_equiv_to_supplied_colimit
    {LimitD : Type*}
    (toLimit : ∀ n : ℕ, Delaunay.DelaunayFlipWord n → LimitD)
    (respects_equiv :
      ∀ {n : ℕ} {W₁ W₂ : Delaunay.DelaunayFlipWord n},
        Delaunay.DelaunayEquiv W₁ W₂ → toLimit n W₁ = toLimit n W₂)
    {n : ℕ} {before after : Delaunay.DelaunayFlipWord n}
    (flip_equiv : Delaunay.DelaunayEquiv before after) :
    toLimit n before = toLimit n after :=
  respects_equiv flip_equiv

/-- A finite equality of Delaunay representatives maps to equality in any supplied cone. -/
theorem delaunay_stage_equality_to_supplied_colimit
    {LimitD : Type*}
    (toLimit : ∀ n : ℕ, Delaunay.DelaunayFlipWord n → LimitD)
    {n : ℕ} {before after : Delaunay.DelaunayFlipWord n}
    (h : before = after) :
    toLimit n before = toLimit n after := by
  rw [h]

end InfoGeometry.Topology.GrandUnificationColimitTransport
