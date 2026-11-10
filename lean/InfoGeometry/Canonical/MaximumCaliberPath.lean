/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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

## BUCKET 1: Path and graph data
Finite path words and graph edge-rate data supply the underlying carriers.

## BUCKET 2: Derived path identities
Positive local rate ratios and their factorization yield the exponential
path-entropy formula by the graph owner's finite-list theorem.

## BUCKET 3: Conditional interfaces
Bayesian projection and variational optimizer claims remain explicit inputs;
this module does not promote them to derived analytic results.
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

The path law stores a local factorization of the forward/backward probability
ratio into the graph's edge-rate ratios, plus positivity of those factors.
The graph owner derives the exponential path-entropy identity from that data.
-/
structure GraphMaxCalPathLaw (PathSample : Type) where
  pathEdges : PathSample → List E
  forwardProbability : PathSample → ℝ
  backwardProbability : PathSample → ℝ
  ratio_factorization : ∀ γ,
    forwardProbability γ / backwardProbability γ =
      G.pathForwardBackwardRatio (pathEdges γ)
  rate_ratio_positive : ∀ γ e, e ∈ pathEdges γ →
    0 < G.forwardRate e / G.reverseRate e

namespace GraphMaxCalPathLaw

variable {G}
variable {PathSample : Type}
variable (L : GraphMaxCalPathLaw G PathSample)

/-- The global MaxCal path ratio follows from local rate factorization and the
positive-rate log/product theorem in the graph owner. -/
theorem forward_backward_ratio_eq_exp_pathEntropy (γ : PathSample) :
    L.forwardProbability γ / L.backwardProbability γ =
      Real.exp (G.pathEntropyProduction (L.pathEdges γ)) := by
  rw [L.ratio_factorization γ]
  exact G.pathForwardBackwardRatio_eq_exp_pathEntropyProduction
    (L.pathEdges γ) (L.rate_ratio_positive γ)

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
    G.pathEntropyProduction C.edges = 0 :=
  G.cycleCurvatureLog_eq_zero_of_logAffinity_eq_coboundary φ C hC hexact

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
    G.DetailedBalanceOnCycle C :=
  (G.logWilsonCycleLaw_of_pos C hpos).detailedBalance_iff_zero_log_curvature.mpr hzero

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
