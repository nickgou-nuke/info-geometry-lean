import InfoGeometry.Canonical.BostConnesSuperalgebraConstructive
import InfoGeometry.Canonical.DAGHodgeOperatorOwnerMap
import InfoGeometry.Canonical.GraphDiracPresentation
import InfoGeometry.Canonical.HodgeDiracLaplacianBridge
import InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus

/-!
# Supergraded Graph / Entropy / Hodge--Dirac Bridge

This file is a narrow composition layer over existing owner surfaces:

* graph energy/readout: `GraphDiracPresentation`;
* finite thermodynamic entropy kernels: `ThermodynamicChiralGraphCalculus`;
* native DAG operator readouts: `DAGHodgeOperatorOwnerMap`;
* Hodge--Dirac algebra: `HodgeDiracLaplacianBridge`;
* Witten parity/supertrace cancellation: `BostConnesSuperalgebraConstructive`.

It does not define a new graph model and does not assert analytic KMS, C*-completion,
zeta, or Riemann-hypothesis consequences.
-/

noncomputable section

namespace InfoGeometry.Canonical.SupergradedGraphEntropyHodgeBridge

open InfoGeometry.Canonical.BostConnesSuperalgebraConstructive
open InfoGeometry.Canonical.DAGHodgeOperatorOwnerMap
open InfoGeometry.Canonical.GraphDiracPresentation
open InfoGeometry.Canonical.HodgeDiracLaplacianBridge
open InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus

/--
Proof-carrying packet tying the graph-energy, Hodge--Dirac, and Witten-parity
lanes together.

The packet stores only the data required by the owner theorems.  It deliberately
does not claim that the algebra `Op` is an infinite UHF/C*-completion, nor that
the graph is a completed analytic spectral triple.
-/
@[rep_depth operator]
structure SupergradedGraphEntropyHodgePacket
    (Op : Type*) [Ring Op] [StarRing Op] where
  /-- Graph-metric Dirac presentation used for scalar energy readout. -/
  graph : GraphMetricDirac
  /-- Algebraic Hodge/Dirac/Laplacian carrier. -/
  hodge : HodgeDiracLaplacianCarrier Op
  /-- Supplied chiral anticommutation of Dirac and Hodge axes. -/
  hodgeChiral : IsDiracHodgeChiral hodge
  /-- Supplied closure law `Δ = Q²`. -/
  laplacianFromDirac : IsLaplacianFromDirac hodge
  /-- Supplied Witten parity involution. -/
  parity : StarWittenParity Op
  /-- Supplied algebraic state. -/
  state : AlgebraicState Op
  /-- State invariance under Witten parity. -/
  stateInvariant : StateParityInvariant parity state
  /-- Operator selected as parity-odd. -/
  oddOperator : Op
  /-- Proof that the selected operator is parity-odd. -/
  oddOperator_parity : ParityOdd parity oddOperator

namespace SupergradedGraphEntropyHodgePacket

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (P : SupergradedGraphEntropyHodgePacket Op)

/-- Graph energy/readout is the distance-to-reference metric readout. -/
@[rep_depth operator]
def graphEnergy (ψ : P.graph.State) : ℝ :=
  P.graph.metricReadout ψ

/-- The graph energy readout is nonnegative by the graph owner contract. -/
@[rep_depth operator]
theorem graphEnergy_nonneg (ψ : P.graph.State) :
    0 ≤ P.graphEnergy ψ :=
  GraphMetricDirac.metricReadout_nonneg P.graph ψ

/-- The supplied Laplacian is Hodge-even when `Δ = Q²` and `{Q,*}=0`. -/
@[rep_depth operator]
theorem laplacian_commutes_hodge :
    laplacian P.hodge * hodgeStar P.hodge =
      hodgeStar P.hodge * laplacian P.hodge :=
  laplacian_commutes_hodge_of_dirac_closure
    P.hodge P.hodgeChiral P.laplacianFromDirac

/-- The selected parity-odd operator has zero Witten supertrace in an invariant state. -/
@[rep_depth operator]
theorem oddOperator_supertrace_zero :
    supertrace P.parity P.state P.oddOperator = 0 :=
  supertrace_eq_zero_of_invariant_state_on_odd
    P.parity P.state P.stateInvariant P.oddOperator_parity

end SupergradedGraphEntropyHodgePacket

/-! ## Entropy-energy kernels from the thermodynamic graph owner -/

/-- Edgewise entropy kernel nonnegativity from positive forward/reverse fluxes. -/
@[rep_depth operator]
theorem edge_entropy_kernel_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ (x - y) * Real.log (x / y) :=
  irreversibleFluxAffinity_nonneg_of_pos hx hy

/--
Finite stochastic entropy production is nonnegative when every forward and
reverse probability flux is positive.  This is a direct owner readout.
-/
@[rep_depth operator]
theorem stochasticEntropyProduction_nonneg_of_positive_flux
    {V E : Type} [Fintype E]
    (G : DirectedThermoGraph V E)
    (hforward : ∀ e, 0 < G.probability (G.src e) * G.forwardRate e)
    (hreverse : ∀ e, 0 < G.probability (G.dst e) * G.reverseRate e) :
    0 ≤ G.stochasticEntropyProduction :=
  DirectedThermoGraph.stochasticEntropyProduction_nonneg_of_positive_flux
    G hforward hreverse

/-! ## DAG operator readouts remain owned by `DAG.GraphHodge` -/

section DAGReadouts

variable {α : Type*} [BEq α] [Hashable α]

/-- Readout that the canonical bridge uses the native DAG graph-Dirac matrix. -/
@[rep_depth operator]
theorem dagGraphDirac_owner_readout (tc : DAG.TwoComplex α) :
    dagGraphDirac tc = DAG.graphDirac tc :=
  dagGraphDirac_eq tc

/-- Readout that the canonical bridge uses the native DAG 0-chain Laplacian. -/
@[rep_depth operator]
theorem dagLaplacian0_owner_readout (tc : DAG.TwoComplex α) :
    dagLaplacian0 tc = DAG.laplacian0 tc :=
  dagLaplacian0_eq tc

/-- Readout that the canonical bridge uses the native DAG 1-chain Hodge Laplacian. -/
@[rep_depth operator]
theorem dagLaplacian1_owner_readout (tc : DAG.TwoComplex α) :
    dagLaplacian1 tc = DAG.laplacian1 tc :=
  dagLaplacian1_eq tc

end DAGReadouts

end InfoGeometry.Canonical.SupergradedGraphEntropyHodgeBridge

end noncomputable section
