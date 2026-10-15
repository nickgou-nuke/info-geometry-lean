import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
* commutation and nilpotent sandwich-zero identities transport through any
  ring homomorphism.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES

All limit statements depend on an explicit map `Stage →+* Limit`.  The loop
closure theorem also depends on the same explicit flat-commutation premise as
the finite-stage theorem.

#### BUCKET 3: OPEN CLOSURE DEBT

A genuine Delaunay/Penrose inductive colimit requires explicit bonding maps
`DelaunayFlipWord n → DelaunayFlipWord (n+1)` and compatibility theorems for
`DelaunayEquiv` and `rohozhkinMatrix`. Those maps are not exposed by the
current Delaunay owner.
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

/-- A ring homomorphism preserves commutation of an arbitrary pair. -/
theorem map_commutation
    (toLimit : Stage →+* Limit) (x y : Stage)
    (h : x * y = y * x) :
    toLimit x * toLimit y = toLimit y * toLimit x := by
  calc
    toLimit x * toLimit y = toLimit (x * y) := (map_mul toLimit x y).symm
    _ = toLimit (y * x) := congrArg toLimit h
    _ = toLimit y * toLimit x := map_mul toLimit y x

/-- A ring homomorphism preserves the symmetric mixed-product sandwich identity
whenever its first factor is square-zero. -/
theorem map_nilpotent_symmetric_mixed_sandwich
    (toLimit : Stage →+* Limit) (N X : Stage)
    (hN : N * N = 0) :
    toLimit N *
        (toLimit N * toLimit X + toLimit X * toLimit N) * toLimit N = 0 := by
  have h := GrandUnificationLinker.nilpotent_sandwich_zero N X hN
  have h' : N * (N * X + X * N) * N = 0 := by
    simpa [GrandUnificationLinker.symmetric_mixed_element] using h
  calc
    toLimit N * (toLimit N * toLimit X + toLimit X * toLimit N) * toLimit N
        = toLimit (N * (N * X + X * N) * N) := by
            simp only [map_mul, map_add]
    _ = 0 := by rw [h', map_zero]

end InfoGeometry.Topology.GrandUnificationColimitTransport
