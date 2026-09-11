import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.MaximumCaliberPath
import InfoGeometry.Canonical.BayesianMarkovChain
import InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus

/-!
# Canonical Maximum Caliber Path Bridge

Canonical readout layer for Jaynes Maximum Caliber over the existing topology
and thermodynamic graph owners.

The topology owner `InfoGeometry.Topology.MaximumCaliberPath` stores the
thermodynamic-curvature path packet.  This file adds:

* graph-path readbacks through `ThermodynamicChiralGraphCalculus`;
* collapse of exact closed-loop path constraints to detailed balance; and
* compatibility with the explicit Bayesian projection socket.

No analytic MaxCal existence theorem, CP map construction, KMS uniqueness
theorem, or continuous path-integral result is asserted here.
-/

namespace InfoGeometry.Canonical.MaximumCaliberPath

open InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus
open InfoGeometry.Canonical.BayesianMarkovChain

universe u

/-! ## Thermodynamic graph path readbacks -/

section ThermodynamicGraph

variable {V E : Type}
variable (G : DirectedThermoGraph V E)

/--
Maximum-caliber path law over the repository-owned thermodynamic graph.

The variational MaxCal derivation is represented by `ratio_eq_exp_pathEntropy`;
the graph owner supplies the meaning of path entropy production as the finite
line integral of the log-affinity connection.
-/
structure GraphMaxCalPathLaw (PathSample : Type) where
  pathEdges : PathSample → List E
  forwardProbability : PathSample → ℝ
  backwardProbability : PathSample → ℝ
  ratio_eq_exp_pathEntropy :
    ∀ γ, forwardProbability γ / backwardProbability γ =
      Real.exp (G.pathEntropyProduction (pathEdges γ))

namespace GraphMaxCalPathLaw

variable {G}
variable {PathSample : Type}
variable (L : GraphMaxCalPathLaw G PathSample)

/-- Convert the MaxCal path law to the generic fluctuation-ratio owner packet. -/
noncomputable def toPathProbabilityRatioLaw :
    InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus.DirectedThermoGraph.PathProbabilityRatioLaw
      PathSample where
  forwardProbability := L.forwardProbability
  backwardProbability := L.backwardProbability
  entropyProduction := fun γ => G.pathEntropyProduction (L.pathEdges γ)
  ratio_law := L.ratio_eq_exp_pathEntropy

/-- Forward/backward path probabilities read as exponentiated graph entropy production. -/
theorem forward_backward_ratio_eq_exp_pathEntropy (γ : PathSample) :
    L.forwardProbability γ / L.backwardProbability γ =
      Real.exp (G.pathEntropyProduction (L.pathEdges γ)) :=
  L.ratio_eq_exp_pathEntropy γ

end GraphMaxCalPathLaw

/-- A cycle is a path whose MaxCal constraint is the additive Wilson curvature. -/
theorem cycle_pathEntropyProduction_eq_cycleCurvatureLog
    (C : InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus.Cycle E) :
    G.pathEntropyProduction C.edges = G.cycleCurvatureLog C :=
  rfl

/--
Flat/exact closed-loop sectors have zero MaxCal path constraint.

This is the graph-owner version of "MaxCal collapses to MaxEnt under detailed
balance": the closed-loop path integral of the log-affinity connection vanishes.
-/
theorem cycle_pathEntropyProduction_eq_zero_of_exact
    (φ : DirectedThermoGraph.GaugeTransform V)
    (C : InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus.Cycle E)
    (hC : G.GaugeClosedCycle C)
    (hexact : ∀ e ∈ C.edges, G.logAffinity e = G.gaugeCoboundary φ e) :
    G.pathEntropyProduction C.edges = 0 := by
  rw [cycle_pathEntropyProduction_eq_cycleCurvatureLog G C]
  exact G.cycleCurvatureLog_eq_zero_of_logAffinity_eq_coboundary φ C hC hexact

/-- Positive-rate path ratios are the graph-owner exponential MaxCal readout. -/
theorem pathForwardBackwardRatio_eq_exp_maxCalConstraint
    (path : List E)
    (hpos : ∀ e ∈ path, 0 < G.forwardRate e / G.reverseRate e) :
    G.pathForwardBackwardRatio path = Real.exp (G.pathEntropyProduction path) :=
  G.pathForwardBackwardRatio_eq_exp_pathEntropyProduction path hpos

/-- Zero MaxCal constraint on a positive cycle gives detailed balance on that cycle. -/
theorem detailedBalanceOnCycle_of_pathEntropyProduction_eq_zero
    (C : InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus.Cycle E)
    (hpos : ∀ e ∈ C.edges, 0 < G.forwardRate e / G.reverseRate e)
    (hzero : G.pathEntropyProduction C.edges = 0) :
    G.DetailedBalanceOnCycle C := by
  rw [(G.logWilsonCycleLaw_of_pos C hpos).detailedBalance_iff_zero_log_curvature]
  simpa [cycle_pathEntropyProduction_eq_cycleCurvatureLog G C] using hzero

end ThermodynamicGraph

/-! ## Bayesian Markov bridge readback -/

/--
Maximum-Caliber / Bayesian-Markov compatibility packet.

It says the chosen Bayesian/Markov update is read as the explicit MaxCal
projection on a finite path space.
-/
structure MaximumCaliberMarkovBridge
    {State : Type u}
    (M : State → State)
    (divergence : State → State → ℝ)
    (constraint : State → Prop)
    (prior posterior : State) where
  projectionWitness :
    TensorLimitStateSpace.IsBayesianProjection divergence constraint prior posterior
  markov_eq_projection : M prior = posterior

namespace MaximumCaliberMarkovBridge

variable
    {State : Type u}
    {M : State → State}
    {divergence : State → State → ℝ}
    {constraint : State → Prop}
    {prior posterior : State}

/-- The Markov step is a Bayesian/MaxCal projection in the supplied witness. -/
theorem markov_step_is_bayesian_projection
    (B : MaximumCaliberMarkovBridge M divergence constraint prior posterior) :
    TensorLimitStateSpace.IsBayesianProjection divergence constraint prior (M prior) :=
  TensorLimitStateSpace.markov_step_is_bayesian_projection
    M divergence constraint prior posterior B.markov_eq_projection B.projectionWitness

/-- The Markov posterior lies in the local constraint manifold. -/
theorem posterior_mem_constraint
    (B : MaximumCaliberMarkovBridge M divergence constraint prior posterior) :
    constraint (M prior) :=
  TensorLimitStateSpace.bayesian_projection_mem
    divergence constraint prior (M prior) (markov_step_is_bayesian_projection B)

/-- The Markov posterior minimizes the supplied divergence over the constraint set. -/
theorem posterior_minimizes
    (B : MaximumCaliberMarkovBridge M divergence constraint prior posterior)
    (s : State) (hs : constraint s) :
    divergence (M prior) prior ≤ divergence s prior :=
  TensorLimitStateSpace.bayesian_projection_minimizes
    divergence constraint prior (M prior) (markov_step_is_bayesian_projection B) s hs

end MaximumCaliberMarkovBridge

end InfoGeometry.Canonical.MaximumCaliberPath
