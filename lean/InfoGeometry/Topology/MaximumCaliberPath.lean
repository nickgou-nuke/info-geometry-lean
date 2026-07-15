import Mathlib
import InfoGeometry.Topology.ThermodynamicGauge
import InfoGeometry.Topology.WilsonLoopThermodynamics

/-!
# Maximum Caliber path bridge

Conservative path-space interface for Jaynes-style maximum caliber updates on
the causal DAG.

This file stays theorem-safe:

* a path is represented as a finite ordered word of local steps;
* a caliber packet records a path-space readout and a curvature readout;
* exact detailed balance collapses the curvature readout to zero;
* the zero-curvature readback is the finite equilibrium interface used by the
  stationary KMS layers elsewhere in the repository.

No analytic path-integral theorem, variational uniqueness theorem, or quantum
Markov semigroup construction is asserted here.
-/

namespace MaximumCaliberPath

open ThermodynamicGauge
open WilsonLoopThermodynamics

universe u

variable {Op : Type u} [Ring Op]

/-- Finite path space for a causal DAG. -/
abbrev PathSpace (Op : Type u) := List Op

/--
Maximum-Caliber packet over a finite causal path.

The stored data are deliberately conservative:

* `path` records the finite trajectory word,
* `pathEntropy` is the path-space readout,
* `caliber` is the corresponding Jaynes caliber scalar,
* both are tied to the curvature trace of a supplied thermodynamic flow.
-/
structure MaximumCaliberPacket (Op : Type u) [Ring Op] [Algebra ℝ Op] where
  flow : CausalNonequilibriumFlow Op
  trace : Op →ₗ[ℝ] ℝ
  path : PathSpace Op
  pathEntropy : ℝ
  caliber : ℝ
  pathEntropy_eq_curvatureTrace :
    pathEntropy = trace (thermodynamic_curvature flow)
  caliber_eq_pathEntropy : caliber = pathEntropy

namespace MaximumCaliberPacket

variable {Op : Type u} [Ring Op] [Algebra ℝ Op]
variable (P : MaximumCaliberPacket Op)

/-- Read back the stored caliber as the stored curvature trace. -/
@[simp]
theorem caliber_eq_curvatureTrace :
    P.caliber = P.trace (thermodynamic_curvature P.flow) := by
  rw [P.caliber_eq_pathEntropy, P.pathEntropy_eq_curvatureTrace]

/-- Exact detailed balance forces the curvature readout to vanish. -/
theorem pathEntropy_eq_zero_of_detailed_balance
    (hdb : entropy_production P.flow = 0) :
    P.pathEntropy = 0 := by
  rw [P.pathEntropy_eq_curvatureTrace]
  have hcurv : thermodynamic_curvature P.flow = 0 :=
    curvature_vanishes_under_detailed_balance (flow := P.flow) hdb
  simp [hcurv]

/-- Exact detailed balance forces the caliber to vanish. -/
theorem caliber_eq_zero_of_detailed_balance
    (hdb : entropy_production P.flow = 0) :
    P.caliber = 0 := by
  rw [P.caliber_eq_pathEntropy]
  exact P.pathEntropy_eq_zero_of_detailed_balance hdb

end MaximumCaliberPacket

/-! ## Explicit MaxCal optimizer and thermodynamic-gauge sockets -/

/-- Abstract finite-path MaxCal variational socket.

The optimizer certificate is explicit: this file does not prove analytic
existence or uniqueness of path-entropy maximizers.
-/
structure MaximumCaliberOptimizer (Path : Type u) where
  caliber : (Path → ℝ) → ℝ
  constraint : (Path → ℝ) → Prop
  optimizer : Path → ℝ
  feasible : constraint optimizer
  maximizes : ∀ μ : Path → ℝ, constraint μ → caliber μ ≤ caliber optimizer

namespace MaximumCaliberOptimizer

variable {Path : Type u} (M : MaximumCaliberOptimizer Path)

end MaximumCaliberOptimizer

/-- A MaxCal transition-asymmetry socket over an existing thermodynamic gauge flow. -/
structure MaximumCaliberThermodynamicBridge (flow : CausalNonequilibriumFlow Op) where
  pathConstraint : Op
  pathConstraint_eq_dlnQ : pathConstraint = flow.d_ln_Q
  commutator_eq_constraint :
    flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward = pathConstraint

namespace MaximumCaliberThermodynamicBridge

variable {flow : CausalNonequilibriumFlow Op}
variable (B : MaximumCaliberThermodynamicBridge flow)

/-- The transition commutator is the supplied MaxCal path constraint. -/
theorem commutator_eq_pathConstraint :
    flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward = B.pathConstraint :=
  B.commutator_eq_constraint

/-- Entropy production is the supplied MaxCal path constraint. -/
theorem entropy_production_eq_pathConstraint :
    entropy_production flow = B.pathConstraint := by
  rw [entropy_production_eq_commutator]
  exact B.commutator_eq_constraint

/-- Entropy production is the de Rham/log-partition current `d_ln_Q`. -/
theorem entropy_production_eq_dlnQ
    (B : MaximumCaliberThermodynamicBridge flow) :
    entropy_production flow = flow.d_ln_Q := by
  exact de_rham_potential_equals_entropy_production_of_commutator flow
    (Eq.trans B.commutator_eq_constraint B.pathConstraint_eq_dlnQ)

end MaximumCaliberThermodynamicBridge

/-- Collapse socket from MaxCal path weights to MaxEnt/KMS state weights in an exact sector. -/
structure MaximumCaliberToMaxEntropyCollapse (Path State : Type u) where
  endpoint : Path → State
  pathWeight : Path → ℝ
  stateWeight : State → ℝ
  exactSector : Prop
  exactWitness : exactSector
  collapse : ∀ γ : Path, exactSector → pathWeight γ = stateWeight (endpoint γ)

namespace MaximumCaliberToMaxEntropyCollapse

variable {Path State : Type u} (C : MaximumCaliberToMaxEntropyCollapse Path State)

/-- In the supplied exact sector, MaxCal path weights reduce to MaxEnt state weights. -/
theorem pathWeight_eq_stateWeight (γ : Path) :
    C.pathWeight γ = C.stateWeight (C.endpoint γ) :=
  C.collapse γ C.exactWitness

end MaximumCaliberToMaxEntropyCollapse

end MaximumCaliberPath
