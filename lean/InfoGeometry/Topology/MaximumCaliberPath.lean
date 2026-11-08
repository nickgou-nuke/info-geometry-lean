import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

namespace InfoGeometry.Topology.MaximumCaliberPath

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
theorem entropy_production_eq_pathConstraint
    (flow : CausalNonequilibriumFlow Op) (pathConstraint : Op)
    (hconstraint :
      flow.P_forward * flow.P_backward -
          flow.P_backward * flow.P_forward = pathConstraint) :
    entropy_production flow = pathConstraint := by
  rw [entropy_production_eq_commutator]
  exact hconstraint

theorem entropy_production_eq_dlnQ
    (flow : CausalNonequilibriumFlow Op)
    (hcomm :
      flow.P_forward * flow.P_backward -
          flow.P_backward * flow.P_forward = flow.d_ln_Q) :
    entropy_production flow = flow.d_ln_Q :=
  de_rham_potential_equals_entropy_production_of_commutator flow hcomm

/-! Collapse laws from MaxCal path weights to MaxEnt/KMS state weights on a
model-selected exact path sector. -/
namespace MaximumCaliberToMaxEntropyCollapse

variable {Path State : Type u}

/-- The exact sector is the subtype of paths on which the collapse law applies. -/
def exactSector (IsExactPath : Path → Prop) :=
  { γ : Path // IsExactPath γ }

/-- In the supplied exact sector, MaxCal path weights reduce to MaxEnt state weights. -/
theorem pathWeight_eq_stateWeight
    (endpoint : Path → State) (pathWeight : Path → ℝ)
    (stateWeight : State → ℝ) (IsExactPath : Path → Prop)
    (collapse : ∀ γ : Path, IsExactPath γ →
      pathWeight γ = stateWeight (endpoint γ))
    (γ : Path) (hγ : IsExactPath γ) :
    pathWeight γ = stateWeight (endpoint γ) :=
  collapse γ hγ

/-- The MaxCal-to-MaxEnt collapse law restricted to the genuine exact sector. -/
theorem pathWeight_eq_stateWeight_on_exactSector
    (endpoint : Path → State) (pathWeight : Path → ℝ)
    (stateWeight : State → ℝ) (IsExactPath : Path → Prop)
    (collapse : ∀ γ : Path, IsExactPath γ →
      pathWeight γ = stateWeight (endpoint γ))
    (γ : exactSector IsExactPath) :
    pathWeight γ.1 = stateWeight (endpoint γ.1) :=
  collapse γ.1 γ.2

end MaximumCaliberToMaxEntropyCollapse

end InfoGeometry.Topology.MaximumCaliberPath
