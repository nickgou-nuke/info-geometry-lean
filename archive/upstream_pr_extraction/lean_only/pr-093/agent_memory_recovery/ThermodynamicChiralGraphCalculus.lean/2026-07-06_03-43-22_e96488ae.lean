import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Thermodynamic chiral graph calculus

A conservative Lean packet for the proposed thermodynamic linear graph λ-calculus.

This file does not assert analytic stochastic-thermodynamic closure.  It only
records a typed syntax/semantics interface, finite directed graph decorations,
Wilson-loop readbacks, and small definitional theorems that later owner modules
can strengthen.
-/

namespace InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus

open Finset

noncomputable section

/-- Scalar stochastic-thermodynamic inequality:
`(x - y) log (x / y) ≥ 0` for positive forward and reverse fluxes.

This is the edgewise positivity kernel used below for entropy production from
stochastic rates. -/
theorem irreversibleFluxAffinity_nonneg_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ (x - y) * Real.log (x / y) := by
  rcases le_total y x with hyx | hxy
  · have hsub : 0 ≤ x - y := sub_nonneg.mpr hyx
    have hdiv : 1 ≤ x / y := by
      rw [le_div_iff₀ hy]
      simpa using hyx
    exact mul_nonneg hsub (Real.log_nonneg hdiv)
  · have hsub : x - y ≤ 0 := sub_nonpos.mpr hxy
    have hdiv_nonneg : 0 ≤ x / y := div_nonneg hx.le hy.le
    have hdiv : x / y ≤ 1 := by
      rw [div_le_iff₀ hy]
      simpa using hxy
    exact mul_nonneg_of_nonpos_of_nonpos hsub (Real.log_nonpos hdiv_nonneg hdiv)

/-- A small de Bruijn-style syntax for graph-building terms. -/
inductive ThermoTerm : Type
  | db : Nat → ThermoTerm
  | lam : ThermoTerm → ThermoTerm
  | app : ThermoTerm → ThermoTerm → ThermoTerm
  | nu : ThermoTerm → ThermoTerm
  | edge : Nat → Nat → ℝ → ℝ → ThermoTerm
  | tensor : ThermoTerm → ThermoTerm → ThermoTerm
  | trace : ThermoTerm → ThermoTerm

/-- A finite cycle witness is represented here by its ordered edge list.

The well-formedness/closure proof is intentionally separated from this readout
packet, so graph-navigation tooling can propose cycles before Lean owner files
prove their incidence closure. -/
structure Cycle (E : Type) where
  edges : List E

/-- Finite directed graph data decorated by stochastic/circuit thermodynamic readouts. -/
structure DirectedThermoGraph (V E : Type) where
  src : E → V
  dst : E → V
  forwardRate : E → ℝ
  reverseRate : E → ℝ
  conductance : E → ℝ
  bias : E → ℝ
  capacity : V → ℝ
  probability : V → ℝ
  potential : V → ℝ
  flow : E → ℝ
  affinity : E → ℝ

namespace DirectedThermoGraph

variable {V E : Type} (G : DirectedThermoGraph V E)

/-- Stochastic-thermodynamic current `p_i k⁺ - p_j k⁻` on an edge. -/
def stochasticCurrent (e : E) : ℝ :=
  G.probability (G.src e) * G.forwardRate e - G.probability (G.dst e) * G.reverseRate e

/-- Circuit current with an internal edge bias. -/
def circuitCurrent (e : E) : ℝ :=
  G.conductance e * (G.potential (G.src e) - G.potential (G.dst e) + G.bias e)

/-- Node storage/readout `q_i = C_i φ_i`. -/
def storedCharge (v : V) : ℝ :=
  G.capacity v * G.potential v

/-- Entropy production proxy `Σ_e J_e A_e` over a finite edge type. -/
def entropyProduction [Fintype E] : ℝ :=
  ∑ e, G.flow e * G.affinity e

/-- Multiplicative Wilson-loop readout for forward/reverse edge-rate ratios. -/
def wilsonLoop (C : Cycle E) : ℝ :=
  (C.edges.map (fun e => G.forwardRate e / G.reverseRate e)).prod

/-- Additive Wilson curvature/affinity readout along an ordered cycle. -/
def cycleCurvature (C : Cycle E) : ℝ :=
  (C.edges.map G.affinity).sum

/-- Detailed balance on this cycle, expressed as a trivial Wilson loop. -/
def DetailedBalanceOnCycle (C : Cycle E) : Prop :=
  wilsonLoop (G := G) C = 1

/-- Chiral thermodynamic drive on this cycle, expressed as a nontrivial Wilson loop. -/
def ChiralDriveOnCycle (C : Cycle E) : Prop :=
  wilsonLoop (G := G) C ≠ 1

@[simp] theorem detailedBalanceOnCycle_iff_wilsonLoop_eq_one (C : Cycle E) :
    DetailedBalanceOnCycle (G := G) C ↔ wilsonLoop (G := G) C = 1 :=
  Iff.rfl

@[simp] theorem chiralDriveOnCycle_iff_wilsonLoop_ne_one (C : Cycle E) :
    ChiralDriveOnCycle (G := G) C ↔ wilsonLoop (G := G) C ≠ 1 :=
  Iff.rfl

@[simp] theorem stochasticCurrent_eq (e : E) :
    G.stochasticCurrent e =
      G.probability (G.src e) * G.forwardRate e -
        G.probability (G.dst e) * G.reverseRate e :=
  rfl

@[simp] theorem circuitCurrent_eq (e : E) :
    G.circuitCurrent e =
      G.conductance e * (G.potential (G.src e) - G.potential (G.dst e) + G.bias e) :=
  rfl

@[simp] theorem storedCharge_eq (v : V) :
    G.storedCharge v = G.capacity v * G.potential v :=
  rfl

/-! ### Log-affinity connection and cycle curvature -/

/-- Additive log-affinity connection on an edge: `a_{ij} = log(k_{ij}/k_{ji})`.

This is the discrete gauge-connection one-cochain whose holonomy around a cycle
gives the Wilson loop.  In equilibrium (detailed balance), this is a coboundary
(exact one-form on the graph). -/
noncomputable def logAffinity (e : E) : ℝ :=
  Real.log (G.forwardRate e / G.reverseRate e)

/-- Additive cycle curvature via the log-affinity connection.

`F(C) = Σ_{e ∈ C} log(k⁺_e / k⁻_e)`

This is the discrete analogue of magnetic flux / electromotive force around
a loop.  Vanishing curvature is equivalent to detailed balance on the cycle. -/
noncomputable def cycleCurvatureLog (C : Cycle E) : ℝ :=
  (C.edges.map G.logAffinity).sum

/-- Stochastic thermodynamic affinity on an edge:
`A_{ij} = log(p_i k⁺ / p_j k⁻)`. -/
noncomputable def stochasticAffinity (e : E) : ℝ :=
  Real.log (G.probability (G.src e) * G.forwardRate e /
    (G.probability (G.dst e) * G.reverseRate e))

/-- Entropy production using the stochastic current and stochastic affinity readouts. -/
noncomputable def stochasticEntropyProduction [Fintype E] : ℝ :=
  ∑ e, G.stochasticCurrent e * G.stochasticAffinity e

@[simp] theorem logAffinity_eq (e : E) :
    G.logAffinity e = Real.log (G.forwardRate e / G.reverseRate e) :=
  rfl

@[simp] theorem cycleCurvatureLog_eq (C : Cycle E) :
    G.cycleCurvatureLog C = (C.edges.map G.logAffinity).sum :=
  rfl

/-! ### Gauge transforms and Wilson-loop curvature invariance -/

@[simp] theorem stochasticAffinity_eq (e : E) :
    G.stochasticAffinity e =
      Real.log (G.probability (G.src e) * G.forwardRate e /
        (G.probability (G.dst e) * G.reverseRate e)) :=
  rfl

/-- A vertex gauge/potential used to shift a discrete log-affinity by a coboundary. -/
abbrev GaugeTransform (V : Type) :=
  V → ℝ

/-- Vertex gauge coboundary on an edge.

Changing local vertex potentials by `φ` shifts an additive edge connection by
`φ(dst e) - φ(src e)`.  This is the graph-theoretic gauge term whose sum around
closed cycles vanishes. -/
def gaugeCoboundary (φ : GaugeTransform V) (e : E) : ℝ :=
  φ (G.dst e) - φ (G.src e)

/-- Boundary/coboundary contribution of a vertex gauge around an ordered cycle. -/
def gaugeBoundaryTerm (φ : GaugeTransform V) (C : Cycle E) : ℝ :=
  (C.edges.map (G.gaugeCoboundary φ)).sum

/-- Gauge-shifted additive log-affinity connection. -/
noncomputable def gaugeShiftedLogAffinity (φ : GaugeTransform V) (e : E) : ℝ :=
  G.logAffinity e + G.gaugeCoboundary φ e

/-- Gauge-shifted additive cycle curvature. -/
noncomputable def gaugeShiftedCycleCurvatureLog
    (φ : GaugeTransform V) (C : Cycle E) : ℝ :=
  (C.edges.map (G.gaugeShiftedLogAffinity φ)).sum

/-- A cycle is gauge-closed when every vertex coboundary telescopes to zero on it.

This isolates the graph-incidence/closure proof from the thermodynamic readout:
an owner module may prove this from an explicit closed walk, while this packet
uses it to recover gauge invariance of cycle curvature. -/
def GaugeClosedCycle (C : Cycle E) : Prop :=
  ∀ φ : GaugeTransform V, G.gaugeBoundaryTerm φ C = 0

@[simp] theorem gaugeCoboundary_eq (φ : GaugeTransform V) (e : E) :
    G.gaugeCoboundary φ e = φ (G.dst e) - φ (G.src e) :=
  rfl

@[simp] theorem gaugeBoundaryTerm_eq (φ : GaugeTransform V) (C : Cycle E) :
    G.gaugeBoundaryTerm φ C = (C.edges.map (G.gaugeCoboundary φ)).sum :=
  rfl

@[simp] theorem gaugeShiftedLogAffinity_eq (φ : GaugeTransform V) (e : E) :
    G.gaugeShiftedLogAffinity φ e = G.logAffinity e + G.gaugeCoboundary φ e :=
  rfl

@[simp] theorem gaugeShiftedCycleCurvatureLog_eq
    (φ : GaugeTransform V) (C : Cycle E) :
    G.gaugeShiftedCycleCurvatureLog φ C =
      (C.edges.map (G.gaugeShiftedLogAffinity φ)).sum :=
  rfl

/-- Gauge-shifted curvature splits into physical log-curvature plus the summed
vertex coboundary. -/
theorem gaugeShiftedCycleCurvatureLog_eq_cycleCurvatureLog_add_boundary
    (φ : GaugeTransform V) (C : Cycle E) :
    G.gaugeShiftedCycleCurvatureLog φ C =
      G.cycleCurvatureLog C + G.gaugeBoundaryTerm φ C := by
  cases C with
  | mk edges =>
    induction edges with
    | nil =>
        simp [gaugeShiftedCycleCurvatureLog, cycleCurvatureLog, gaugeBoundaryTerm]
    | cons e es ih =>
        have ih' :
            (List.map (G.gaugeShiftedLogAffinity φ) es).sum =
              (List.map G.logAffinity es).sum +
                (List.map (G.gaugeCoboundary φ) es).sum := by
          simpa [gaugeShiftedCycleCurvatureLog, cycleCurvatureLog, gaugeBoundaryTerm]
            using ih
        simp [gaugeShiftedCycleCurvatureLog, cycleCurvatureLog, gaugeBoundaryTerm,
          gaugeShiftedLogAffinity, gaugeCoboundary, ih']
        ring

/-- Wilson-loop log-curvature is invariant under vertex gauge shifts on a
closed cycle.  This is the theorem-safe Lean form of the gauge-theory reading:
local potentials may change the edge connection, but closed-cycle curvature is a
gauge-invariant observable. -/
theorem gaugeShiftedCycleCurvatureLog_eq_cycleCurvatureLog_of_closed
    (φ : GaugeTransform V) (C : Cycle E) (hC : G.GaugeClosedCycle C) :
    G.gaugeShiftedCycleCurvatureLog φ C = G.cycleCurvatureLog C := by
  rw [G.gaugeShiftedCycleCurvatureLog_eq_cycleCurvatureLog_add_boundary, hC φ]
  ring

/-- Compatibility spelling: closed-cycle log-curvature is invariant under a
vertex gauge transform. -/
theorem cycleCurvatureLog_gauge_invariant
    (φ : GaugeTransform V) (C : Cycle E) (hC : G.GaugeClosedCycle C) :
    G.gaugeShiftedCycleCurvatureLog φ C = G.cycleCurvatureLog C :=
  G.gaugeShiftedCycleCurvatureLog_eq_cycleCurvatureLog_of_closed φ C hC

/-- If the log-affinity is a pure vertex coboundary, every gauge-closed cycle
has zero additive curvature.  This is the conservative Kolmogorov/Polettini
`exact connection ⇒ trivial cycle affinity` direction. -/
theorem cycleCurvatureLog_eq_zero_of_logAffinity_eq_coboundary
    (φ : GaugeTransform V) (C : Cycle E)
    (hC : G.GaugeClosedCycle C)
    (hexact : ∀ e ∈ C.edges, G.logAffinity e = G.gaugeCoboundary φ e) :
    G.cycleCurvatureLog C = 0 := by
  simp only [cycleCurvatureLog]
  calc
    (C.edges.map G.logAffinity).sum = (C.edges.map (G.gaugeCoboundary φ)).sum := by
      congr 1
      apply List.map_congr_left
      intro e he
      exact hexact e he
    _ = G.gaugeBoundaryTerm φ C := by
      rfl
    _ = 0 := hC φ

/-- Compatibility spelling using the expanded boundary term. -/
theorem cycleCurvatureLog_eq_zero_of_logAffinity_eq_gaugeBoundary
    (φ : GaugeTransform V) (C : Cycle E)
    (hC : G.GaugeClosedCycle C)
    (hexact : ∀ e ∈ C.edges,
      G.logAffinity e = φ (G.dst e) - φ (G.src e)) :
    G.cycleCurvatureLog C = 0 :=
  G.cycleCurvatureLog_eq_zero_of_logAffinity_eq_coboundary φ C hC (by
    intro e he
    exact hexact e he)

/-- Owner-facing hypothesis packet for the log/product Wilson identity on one cycle.

The analytic proof of this law needs positivity of all rate ratios plus a list
`log`/`prod` exchange theorem.  The packet keeps the boundary explicit without
using placeholder proofs: a later owner module may construct this structure from those
positivity assumptions. -/
structure LogWilsonCycleLaw (C : Cycle E) : Prop where
  detailedBalance_iff_zero_log_curvature :
    G.DetailedBalanceOnCycle C ↔ G.cycleCurvatureLog C = 0

/-- Global detailed balance relative to a chosen family of cycles. -/
def GlobalDetailedBalance (cycles : Set (Cycle E)) : Prop :=
  ∀ C, C ∈ cycles → G.DetailedBalanceOnCycle C

/-- Every Wilson loop in the chosen cycle family is trivial. -/
def AllWilsonLoopsTrivial (cycles : Set (Cycle E)) : Prop :=
  ∀ C, C ∈ cycles → wilsonLoop (G := G) C = 1

/-- Every additive log-curvature in the chosen cycle family vanishes. -/
def AllLogCurvaturesVanish (cycles : Set (Cycle E)) : Prop :=
  ∀ C, C ∈ cycles → G.cycleCurvatureLog C = 0

/-- Global detailed balance is definitionally the triviality of all chosen
Wilson loops. -/
theorem globalDetailedBalance_iff_allWilsonLoopsTrivial (cycles : Set (Cycle E)) :
    G.GlobalDetailedBalance cycles ↔ G.AllWilsonLoopsTrivial cycles :=
  Iff.rfl

/-- Compatibility spelling for the Kolmogorov-cycle style readout:
global detailed balance is exactly trivial Wilson loop on every selected cycle. -/
theorem detailedBalance_iff_all_cycle_wilsonLoop_eq_one (cycles : Set (Cycle E)) :
    G.GlobalDetailedBalance cycles ↔ ∀ C, C ∈ cycles → wilsonLoop (G := G) C = 1 :=
  Iff.rfl

/-! ### Schnakenberg/Polettini cycle-cocycle interfaces -/

/-- Edge-field shorthand for flows, currents, and additive affinities. -/
abbrev EdgeField := E → ℝ

/-- Vertex divergence/incidence readout of an edge field.

This is the finite graph incidence map in function form: outgoing contribution
minus incoming contribution at each vertex.  It is kept as a computable readout
rather than a heavy `LinearMap`, so later metric/Hodge owner modules can choose
their preferred inner product without changing this API. -/
def incidenceMap [Fintype E] [DecidableEq V] (J : EdgeField (E := E)) (v : V) : ℝ :=
  (∑ e, if G.src e = v then J e else 0) -
    ∑ e, if G.dst e = v then J e else 0

/-- An edge field is a pure gradient/gauge coboundary. -/
def IsGradientFlow (J : EdgeField (E := E)) : Prop :=
  ∃ φ : GaugeTransform V, ∀ e, J e = G.gaugeCoboundary φ e

/-- An edge field is cyclic when its incidence/divergence vanishes at each vertex. -/
def IsCycleFlow [Fintype E] [DecidableEq V] (J : EdgeField (E := E)) : Prop :=
  ∀ v, G.incidenceMap J v = 0

@[simp] theorem incidenceMap_eq [Fintype E] [DecidableEq V]
    (J : EdgeField (E := E)) (v : V) :
    G.incidenceMap J v =
      (∑ e, if G.src e = v then J e else 0) -
        ∑ e, if G.dst e = v then J e else 0 :=
  rfl

/-- Projection data for a Schnakenberg/Polettini cycle-cocycle decomposition.

The full orthogonal projection theorem depends on the chosen conductance/inner
product metric.  This structure is the theorem-safe owner boundary: once an
owner module constructs `gradientPart` and `cyclePart`, this file can expose the
unique decomposition and its physical readbacks without pretending to own the
linear algebra. -/
structure SchnakenbergDecomposition [Fintype E] [DecidableEq V] (A : EdgeField (E := E)) where
  gradientPart : EdgeField (E := E)
  cyclePart : EdgeField (E := E)
  gradient_certificate : G.IsGradientFlow gradientPart
  cycle_certificate : G.IsCycleFlow cyclePart
  reconstruct : ∀ e, A e = gradientPart e + cyclePart e
  unique : ∀ B C : EdgeField (E := E),
    G.IsGradientFlow B → G.IsCycleFlow C → (∀ e, A e = B e + C e) →
      B = gradientPart ∧ C = cyclePart

/-- Read back the Schnakenberg decomposition as an existence-and-uniqueness theorem
from its metric/owner certificate. -/
theorem schnakenberg_decomposition [Fintype E] [DecidableEq V]
    (A : EdgeField (E := E)) (H : G.SchnakenbergDecomposition A) :
    ∃! P : EdgeField (E := E) × EdgeField (E := E),
      G.IsGradientFlow P.1 ∧ G.IsCycleFlow P.2 ∧ ∀ e, A e = P.1 e + P.2 e := by
  refine ⟨(H.gradientPart, H.cyclePart), ⟨H.gradient_certificate, H.cycle_certificate,
    H.reconstruct⟩, ?_⟩
  intro P hP
  rcases P with ⟨B, C⟩
  rcases hP with ⟨hB, hC, hrec⟩
  rcases H.unique B C hB hC hrec with ⟨rfl, rfl⟩
  rfl

/-- A pure gradient component has zero additive Wilson curvature on every
gauge-closed cycle. -/
theorem cycleCurvatureLog_of_gradient_eq_zero
    (A : EdgeField (E := E)) (C : Cycle E)
    (hgrad : G.IsGradientFlow A) (hC : G.GaugeClosedCycle C)
    (hlog : ∀ e ∈ C.edges, G.logAffinity e = A e) :
    G.cycleCurvatureLog C = 0 := by
  rcases hgrad with ⟨φ, hφ⟩
  exact G.cycleCurvatureLog_eq_zero_of_logAffinity_eq_coboundary φ C hC (by
    intro e he
    rw [hlog e he, hφ e])

/-! ### Discrete no-pumping interface -/

/-- A time-indexed thermodynamic graph.  We use finite/discrete time here to keep
Mandal--Jarzynski style pumping constraints algebraic and fast; continuous-time
integration can later be an owner layer over this readout. -/
structure DrivenThermoGraph (Time : Type) where
  graphAt : Time → DirectedThermoGraph V E

/-- Discrete pumped-current/holonomy readout over one driving period. -/
noncomputable def DrivenThermoGraph.integratedPumpedCurrent {Time : Type} [Fintype Time]
    (D : DrivenThermoGraph (V := V) (E := E) Time) (C : Cycle E) : ℝ :=
  ∑ t, (D.graphAt t).cycleCurvatureLog C

/-- Barrier-only driving packet: at each time the cycle log-affinity is exact and
the chosen cycle is gauge-closed.  This is the algebraic no-pumping hypothesis. -/
structure DrivenThermoGraph.BarrierDrivenGraph {Time : Type} [Fintype Time]
    (D : DrivenThermoGraph (V := V) (E := E) Time) (C : Cycle E) where
  gaugeClosed : ∀ t, (D.graphAt t).GaugeClosedCycle C
  exactConnection : ∀ t, ∃ φ : DirectedThermoGraph.GaugeTransform V,
    ∀ e ∈ C.edges, (D.graphAt t).logAffinity e = (D.graphAt t).gaugeCoboundary φ e

/-- At every time slice, a barrier-driven graph has zero cycle curvature. -/
theorem DrivenThermoGraph.cycleCurvatureLog_eq_zero_of_barrierDriven {Time : Type}
    [Fintype Time] (D : DrivenThermoGraph (V := V) (E := E) Time)
    (C : Cycle E) (H : D.BarrierDrivenGraph C) (t : Time) :
    (D.graphAt t).cycleCurvatureLog C = 0 := by
  rcases H.exactConnection t with ⟨φ, hφ⟩
  exact (D.graphAt t).cycleCurvatureLog_eq_zero_of_logAffinity_eq_coboundary φ C
    (H.gaugeClosed t) hφ

/-- Discrete algebraic no-pumping theorem: if the driven graph remains exact on
the cycle for every time slice, the integrated pumped curvature/current is zero. -/
theorem DrivenThermoGraph.no_pumping_theorem {Time : Type} [Fintype Time]
    (D : DrivenThermoGraph (V := V) (E := E) Time)
    (C : Cycle E) (H : D.BarrierDrivenGraph C) :
    D.integratedPumpedCurrent C = 0 := by
  rw [integratedPumpedCurrent]
  exact Finset.sum_eq_zero (fun t _ => D.cycleCurvatureLog_eq_zero_of_barrierDriven C H t)

/-! ### Finite-path fluctuation theorem interface -/

/-- Time-reversal readout obtained by swapping forward and reverse rates while
leaving the incidence convention fixed. -/
def timeReversedGraph : DirectedThermoGraph V E where
  src := G.src
  dst := G.dst
  forwardRate := G.reverseRate
  reverseRate := G.forwardRate
  conductance := G.conductance
  bias := fun e => -G.bias e
  capacity := G.capacity
  probability := G.probability
  potential := G.potential
  flow := fun e => -G.flow e
  affinity := fun e => -G.affinity e

/-- Entropy production along a finite ordered path of edges, using log-rate ratios. -/
noncomputable def pathEntropyProduction (path : List E) : ℝ :=
  (path.map G.logAffinity).sum

/-- Multiplicative forward/backward path probability ratio from edge-rate ratios. -/
def pathForwardBackwardRatio (path : List E) : ℝ :=
  (path.map (fun e => G.forwardRate e / G.reverseRate e)).prod

@[simp] theorem timeReversedGraph_forwardRate (e : E) :
    G.timeReversedGraph.forwardRate e = G.reverseRate e :=
  rfl

@[simp] theorem timeReversedGraph_reverseRate (e : E) :
    G.timeReversedGraph.reverseRate e = G.forwardRate e :=
  rfl

@[simp] theorem pathEntropyProduction_eq (path : List E) :
    G.pathEntropyProduction path = (path.map G.logAffinity).sum :=
  rfl

/-- Finite-path ratio equals the exponential of path entropy production under
positive rate ratios. -/
theorem pathForwardBackwardRatio_eq_exp_pathEntropyProduction
    (path : List E)
    (hpos : ∀ e ∈ path, 0 < G.forwardRate e / G.reverseRate e) :
    G.pathForwardBackwardRatio path = Real.exp (G.pathEntropyProduction path) := by
  simp only [pathForwardBackwardRatio, pathEntropyProduction]
  rw [Real.exp_list_sum]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro e he
  simp only [Function.comp_def, logAffinity]
  exact (Real.exp_log (hpos e he)).symm

/-- Abstract finite-ensemble integral fluctuation law: the expectation of
`exp(-σ)` is one.  The expectation functional is supplied by the owner
probability model over paths. -/
structure IntegralFluctuationLaw (PathSample : Type) where
  entropyProduction : PathSample → ℝ
  expectation : (PathSample → ℝ) → ℝ
  exp_neg_entropy_expectation_eq_one :
    expectation (fun ω => Real.exp (-(entropyProduction ω))) = 1

/-- Integral fluctuation theorem readback from the owner probability packet. -/
theorem integral_fluctuation_theorem {PathSample : Type}
    (L : IntegralFluctuationLaw PathSample) :
    L.expectation (fun ω => Real.exp (-(L.entropyProduction ω))) = 1 :=
  L.exp_neg_entropy_expectation_eq_one

/-- A path-level Gallavotti--Cohen style ratio packet connecting forward/backward
path probabilities to entropy production. -/
structure PathProbabilityRatioLaw (PathSample : Type) where
  forwardProbability : PathSample → ℝ
  backwardProbability : PathSample → ℝ
  entropyProduction : PathSample → ℝ
  ratio_law : ∀ ω, forwardProbability ω / backwardProbability ω =
    Real.exp (entropyProduction ω)

/-- Forward/backward path probability ratio equals exponentiated path entropy
production by direct readback from the owner law. -/
theorem forward_backward_path_probability_ratio_eq_exp_entropy
    {PathSample : Type} (L : PathProbabilityRatioLaw PathSample) (ω : PathSample) :
    L.forwardProbability ω / L.backwardProbability ω = Real.exp (L.entropyProduction ω) :=
  L.ratio_law ω

/-- Read back the detailed-balance/log-curvature equivalence from an owner law. -/
theorem detailedBalanceOnCycle_iff_cycleCurvatureLog_eq_zero_of_law
    (C : Cycle E) (H : G.LogWilsonCycleLaw C) :
    G.DetailedBalanceOnCycle C ↔ G.cycleCurvatureLog C = 0 :=
  H.detailedBalance_iff_zero_log_curvature

/-- Auxiliary: the Wilson loop equals `exp` of the additive log-curvature,
under positivity of all rate ratios along the cycle.

`W(C) = ∏ (k⁺/k⁻) = exp(Σ log(k⁺/k⁻)) = exp(F(C))`

This is the fundamental `exp ∘ log` bridge between the multiplicative and
additive Wilson-loop readouts. -/
theorem wilsonLoop_eq_exp_cycleCurvatureLog
    (C : Cycle E)
    (hpos : ∀ e ∈ C.edges, 0 < G.forwardRate e / G.reverseRate e) :
    wilsonLoop (G := G) C = Real.exp (G.cycleCurvatureLog C) := by
  simp only [wilsonLoop, cycleCurvatureLog]
  rw [Real.exp_list_sum]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro e he
  simp only [Function.comp_def, logAffinity]
  exact (Real.exp_log (hpos e he)).symm

/-- Product Wilson triviality is equivalent to vanishing additive log-curvature
on one positive-rate cycle. -/
theorem wilsonLoop_eq_one_iff_cycleCurvatureLog_eq_zero_of_pos
    (C : Cycle E)
    (hpos : ∀ e ∈ C.edges, 0 < G.forwardRate e / G.reverseRate e) :
    wilsonLoop (G := G) C = 1 ↔ G.cycleCurvatureLog C = 0 := by
  rw [G.wilsonLoop_eq_exp_cycleCurvatureLog C hpos, Real.exp_eq_one_iff]

/-- Construct a `LogWilsonCycleLaw` from the positivity of all rate ratios on
the cycle.  This is the constructive owner proof that fills the abstract
`LogWilsonCycleLaw` packet. -/
theorem logWilsonCycleLaw_of_pos
    (C : Cycle E)
    (hpos : ∀ e ∈ C.edges, 0 < G.forwardRate e / G.reverseRate e) :
    G.LogWilsonCycleLaw C where
  detailedBalance_iff_zero_log_curvature := by
    rw [DetailedBalanceOnCycle, G.wilsonLoop_eq_exp_cycleCurvatureLog C hpos,
        Real.exp_eq_one_iff]

/-- Under positivity on every selected cycle, global detailed balance is
equivalent to vanishing log-curvature on every selected cycle. -/
theorem globalDetailedBalance_iff_allLogCurvaturesVanish_of_pos
    (cycles : Set (Cycle E))
    (hpos : ∀ C, C ∈ cycles → ∀ e ∈ C.edges, 0 < G.forwardRate e / G.reverseRate e) :
    G.GlobalDetailedBalance cycles ↔ G.AllLogCurvaturesVanish cycles := by
  constructor
  · intro hDB C hC
    exact
      (G.logWilsonCycleLaw_of_pos C (hpos C hC)).detailedBalance_iff_zero_log_curvature.1
        (hDB C hC)
  · intro hLog C hC
    exact
      (G.logWilsonCycleLaw_of_pos C (hpos C hC)).detailedBalance_iff_zero_log_curvature.2
        (hLog C hC)

/-! ### Kirchhoff conservation law -/

/-- Net outgoing current from a vertex: `Σ_{e : src e = v} I_e - Σ_{e : dst e = v} I_e`.

This is the discrete divergence of the current field.  Kirchhoff's current law
asserts `q̇_v = -kirchhoffDivergence G v`, i.e. charge conservation. -/
def kirchhoffDivergence [Fintype E] [DecidableEq V] (v : V) : ℝ :=
  ∑ e, if G.src e = v then G.flow e else 0
    - ∑ e, if G.dst e = v then G.flow e else 0

/-- Kirchhoff conservation law as a predicate: the rate of change of stored
charge equals the negative divergence of current. -/
structure KirchhoffConservation [Fintype E] [DecidableEq V] where
  chargeRate : V → ℝ
  conservation : ∀ v, chargeRate v = -G.kirchhoffDivergence v

/-! ### Entropy production nonnegativity -/

/-- Entropy production nonnegativity certificate.

This is still semantic: pointwise nonnegativity is supplied by an owner proof,
while total nonnegativity follows by summing finite nonnegative contributions. -/
structure EntropyProductionNonneg [Fintype E] where
  pointwise_nonneg : ∀ e, 0 ≤ G.flow e * G.affinity e
  total_nonneg : 0 ≤ G.entropyProduction

/-- If every edge contribution is nonnegative, the finite entropy-production
readout is nonnegative. -/
theorem entropyProduction_nonneg_of_pointwise [Fintype E]
    (h : ∀ e, 0 ≤ G.flow e * G.affinity e) :
    0 ≤ G.entropyProduction := by
  simpa [entropyProduction] using Finset.sum_nonneg (fun e _ => h e)

/-- Edgewise nonnegativity for stochastic current times stochastic affinity
from positivity of the forward and reverse probability fluxes. -/
theorem stochasticCurrent_mul_stochasticAffinity_nonneg_of_positive_flux
    (e : E)
    (hforward : 0 < G.probability (G.src e) * G.forwardRate e)
    (hreverse : 0 < G.probability (G.dst e) * G.reverseRate e) :
    0 ≤ G.stochasticCurrent e * G.stochasticAffinity e := by
  simpa [stochasticCurrent, stochasticAffinity] using
    irreversibleFluxAffinity_nonneg_of_pos
      (x := G.probability (G.src e) * G.forwardRate e)
      (y := G.probability (G.dst e) * G.reverseRate e)
      hforward hreverse

/-- Stochastic entropy production is nonnegative when every forward and reverse
probability flux is positive. -/
theorem stochasticEntropyProduction_nonneg_of_positive_flux [Fintype E]
    (hforward : ∀ e, 0 < G.probability (G.src e) * G.forwardRate e)
    (hreverse : ∀ e, 0 < G.probability (G.dst e) * G.reverseRate e) :
    0 ≤ G.stochasticEntropyProduction := by
  simpa [stochasticEntropyProduction] using
    Finset.sum_nonneg
      (fun e _ =>
        G.stochasticCurrent_mul_stochasticAffinity_nonneg_of_positive_flux e
          (hforward e) (hreverse e))

/-- The stored entropy-production readout is nonnegative when its `flow` and
`affinity` fields are calibrated to the stochastic current and stochastic
affinity, and all stochastic probability fluxes are positive. -/
theorem entropyProduction_nonneg_of_stochastic_rates [Fintype E]
    (hflow : ∀ e, G.flow e = G.stochasticCurrent e)
    (haffinity : ∀ e, G.affinity e = G.stochasticAffinity e)
    (hforward : ∀ e, 0 < G.probability (G.src e) * G.forwardRate e)
    (hreverse : ∀ e, 0 < G.probability (G.dst e) * G.reverseRate e) :
    0 ≤ G.entropyProduction := by
  refine G.entropyProduction_nonneg_of_pointwise ?_
  intro e
  rw [hflow e, haffinity e]
  exact
    G.stochasticCurrent_mul_stochasticAffinity_nonneg_of_positive_flux e
      (hforward e) (hreverse e)

/-- Build the entropy-production nonnegativity certificate from pointwise edge
certificates. -/
def entropyProductionNonnegOfPointwise [Fintype E]
    (h : ∀ e, 0 ≤ G.flow e * G.affinity e) :
    G.EntropyProductionNonneg where
  pointwise_nonneg := h
  total_nonneg := G.entropyProduction_nonneg_of_pointwise h

/-! ### Equilibrium existence and uniqueness -/

/-- Candidate-distribution current on an edge. -/
def edgeCurrentOf (π : V → ℝ) (e : E) : ℝ :=
  π (G.src e) * G.forwardRate e - π (G.dst e) * G.reverseRate e

/-- Master-equation residual at a vertex, written as current divergence. -/
def stationaryResidual [Fintype E] [DecidableEq V] (π : V → ℝ) (v : V) : ℝ :=
  ∑ e, if G.src e = v then G.edgeCurrentOf π e else 0
    - ∑ e, if G.dst e = v then G.edgeCurrentOf π e else 0

/-- A normalized nonnegative distribution with zero master-equation residual. -/
def IsStationaryDistribution [Fintype V] [Fintype E] [DecidableEq V]
    (π : V → ℝ) : Prop :=
  (∀ v, 0 ≤ π v) ∧ (∑ v, π v = 1) ∧ ∀ v, G.stationaryResidual π v = 0

/-- Equilibrium distribution: stationary, with each pairwise edge current zero. -/
def IsEquilibriumDistribution [Fintype V] [Fintype E] [DecidableEq V]
    (π : V → ℝ) : Prop :=
  G.IsStationaryDistribution π ∧ ∀ e, G.edgeCurrentOf π e = 0

/-- Edgewise detailed balance implies the stationarity part of equilibrium. -/
theorem isStationaryDistribution_of_edgeCurrent_eq_zero
    [Fintype V] [Fintype E] [DecidableEq V]
    {π : V → ℝ}
    (hnonneg : ∀ v, 0 ≤ π v)
    (hnormalized : ∑ v, π v = 1)
    (hcurrent : ∀ e, G.edgeCurrentOf π e = 0) :
    G.IsStationaryDistribution π := by
  refine ⟨hnonneg, hnormalized, ?_⟩
  intro v
  simp [stationaryResidual, hcurrent]

/-- Edgewise detailed balance plus normalization/nonnegativity gives an
equilibrium distribution. -/
theorem isEquilibriumDistribution_of_edgeCurrent_eq_zero
    [Fintype V] [Fintype E] [DecidableEq V]
    {π : V → ℝ}
    (hnonneg : ∀ v, 0 ≤ π v)
    (hnormalized : ∑ v, π v = 1)
    (hcurrent : ∀ e, G.edgeCurrentOf π e = 0) :
    G.IsEquilibriumDistribution π :=
  ⟨G.isStationaryDistribution_of_edgeCurrent_eq_zero hnonneg hnormalized hcurrent, hcurrent⟩

/-- Proof-carrying owner surface for equilibrium existence and uniqueness. -/
structure EquilibriumExistenceUniqueness
    [Fintype V] [Fintype E] [DecidableEq V] where
  distribution : V → ℝ
  isEquilibrium : G.IsEquilibriumDistribution distribution
  unique : ∀ π, G.IsEquilibriumDistribution π → π = distribution

/-- Read back existence and uniqueness from the owner certificate. -/
theorem existsUnique_equilibriumDistribution
    [Fintype V] [Fintype E] [DecidableEq V]
    (H : G.EquilibriumExistenceUniqueness) :
    ∃! π : V → ℝ, G.IsEquilibriumDistribution π := by
  refine ⟨H.distribution, H.isEquilibrium, ?_⟩
  intro π hπ
  exact H.unique π hπ

end DirectedThermoGraph

/-- Explicit three-edge chiral triangle readout.

The names follow the prose source: `AB, BC, CA` are the oriented rates and
`BA, CB, AC` are their reverse rates. -/
structure ChiralTriangleRates where
  kAB : ℝ
  kBA : ℝ
  kBC : ℝ
  kCB : ℝ
  kCA : ℝ
  kAC : ℝ

namespace ChiralTriangleRates

/-- Wilson loop of the oriented triangle `A → B → C → A`. -/
def wilsonLoop (T : ChiralTriangleRates) : ℝ :=
  T.kAB * T.kBC * T.kCA / (T.kBA * T.kCB * T.kAC)

/-- Additive log-curvature of the oriented triangle. -/
def logCurvature (T : ChiralTriangleRates) : ℝ :=
  Real.log (T.kAB / T.kBA) + Real.log (T.kBC / T.kCB) + Real.log (T.kCA / T.kAC)

/-- Product form of the triangle Wilson loop, exposed as a readback theorem. -/
@[simp] theorem wilsonLoop_eq (T : ChiralTriangleRates) :
    T.wilsonLoop = T.kAB * T.kBC * T.kCA / (T.kBA * T.kCB * T.kAC) :=
  rfl

/-- Additive log-curvature readback theorem. -/
@[simp] theorem logCurvature_eq (T : ChiralTriangleRates) :
    T.logCurvature =
      Real.log (T.kAB / T.kBA) + Real.log (T.kBC / T.kCB) +
        Real.log (T.kCA / T.kAC) :=
  rfl

/-- Triangle-level detailed balance readout. -/
def DetailedBalance (T : ChiralTriangleRates) : Prop :=
  T.wilsonLoop = 1

/-- Triangle-level chiral drive readout. -/
def ChiralDrive (T : ChiralTriangleRates) : Prop :=
  T.wilsonLoop ≠ 1

@[simp] theorem detailedBalance_iff_wilsonLoop_eq_one (T : ChiralTriangleRates) :
    T.DetailedBalance ↔ T.wilsonLoop = 1 :=
  Iff.rfl

@[simp] theorem chiralDrive_iff_wilsonLoop_ne_one (T : ChiralTriangleRates) :
    T.ChiralDrive ↔ T.wilsonLoop ≠ 1 :=
  Iff.rfl

@[simp] theorem not_chiralDrive_of_detailedBalance {T : ChiralTriangleRates}
    (hT : T.DetailedBalance) : ¬ T.ChiralDrive := by
  intro hχ
  exact hχ hT

end ChiralTriangleRates

/-- Vertices of the explicit triangle example. -/
inductive TriangleVertex : Type
  | A | B | C
  deriving DecidableEq

/-- Oriented edges of the explicit triangle example. -/
inductive TriangleEdge : Type
  | AB | BC | CA
  deriving DecidableEq

namespace ChiralTriangleGraph