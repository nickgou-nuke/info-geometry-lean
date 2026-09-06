namespace ChiralTriangleGraph

/-- Interpret triangle rates as a three-edge decorated thermodynamic graph. -/
def graph (T : ChiralTriangleRates) : DirectedThermoGraph TriangleVertex TriangleEdge where
  src
    | TriangleEdge.AB => TriangleVertex.A
    | TriangleEdge.BC => TriangleVertex.B
    | TriangleEdge.CA => TriangleVertex.C
  dst
    | TriangleEdge.AB => TriangleVertex.B
    | TriangleEdge.BC => TriangleVertex.C
    | TriangleEdge.CA => TriangleVertex.A
  forwardRate
    | TriangleEdge.AB => T.kAB
    | TriangleEdge.BC => T.kBC
    | TriangleEdge.CA => T.kCA
  reverseRate
    | TriangleEdge.AB => T.kBA
    | TriangleEdge.BC => T.kCB
    | TriangleEdge.CA => T.kAC
  -- DEBT_ID: CTG_TRIVIAL_READOUTS
  -- DEBT_KIND: ZERO_DATUM
  -- ZERO_DATUM: Trivial placeholders for triangle graph model
  conductance := fun _ => 0
  bias := fun _ => 0
  capacity := fun _ => 0
  probability := fun _ => 0
  potential := fun _ => 0
  flow := fun _ => 0
  affinity := fun _ => 0

/-- The ordered oriented triangle cycle `A → B → C → A`. -/
def cycle : Cycle TriangleEdge where
  edges := [TriangleEdge.AB, TriangleEdge.BC, TriangleEdge.CA]

/-- The generic graph Wilson-loop readout specializes to the triangle product. -/
theorem graph_wilsonLoop_eq_triangle (T : ChiralTriangleRates) :
    DirectedThermoGraph.wilsonLoop (graph T) cycle =
      (T.kAB / T.kBA) * (T.kBC / T.kCB) * (T.kCA / T.kAC) := by
  simp [DirectedThermoGraph.wilsonLoop, graph, cycle]
  ring

/-- Triangle detailed balance can be read through the generic cycle predicate
when the generic Wilson loop is written in ratio-product form. -/
theorem detailedBalance_iff_graph_cycle_ratio_product_eq_one (T : ChiralTriangleRates) :
    DirectedThermoGraph.DetailedBalanceOnCycle (graph T) cycle ↔
      (T.kAB / T.kBA) * (T.kBC / T.kCB) * (T.kCA / T.kAC) = 1 := by
  simp [DirectedThermoGraph.DetailedBalanceOnCycle, graph_wilsonLoop_eq_triangle]

/-- The oriented triangle cycle is gauge-closed: vertex coboundaries telescope. -/
theorem graph_cycleGaugeClosed (T : ChiralTriangleRates) :
    DirectedThermoGraph.GaugeClosedCycle (graph T) cycle := by
  intro φ
  simp [DirectedThermoGraph.gaugeBoundaryTerm, DirectedThermoGraph.gaugeCoboundary, graph, cycle]

/-- Gauge-shifted log-curvature on the triangle agrees with the original
log-curvature. -/
theorem graph_cycleCurvatureLog_gauge_invariant
    (T : ChiralTriangleRates)
    (φ : DirectedThermoGraph.GaugeTransform TriangleVertex) :
    DirectedThermoGraph.gaugeShiftedCycleCurvatureLog (graph T) φ cycle =
      DirectedThermoGraph.cycleCurvatureLog (graph T) cycle := by
  exact
    DirectedThermoGraph.cycleCurvatureLog_gauge_invariant (graph T) φ cycle
      (graph_cycleGaugeClosed T)

end ChiralTriangleGraph

/-- Conservative interface packet connecting de Bruijn syntax to decorated graph semantics.

The fields are deliberately proof-carrying assumptions/witnesses, not analytic
closure claims.  Later modules can replace these fields by owner theorems. -/
structure ThermodynamicGraphLambdaPacket where
  term : ThermoTerm
  Vertex : Type
  Edge : Type
  graph : DirectedThermoGraph Vertex Edge
  semanticInterpretation : Prop
  linearResourceDiscipline : Prop
  probabilisticSemantics : Prop
  circuitSemantics : Prop
  wilsonLoopSemantics : Prop
  semanticInterpretation_cert : semanticInterpretation
  linearResourceDiscipline_cert : linearResourceDiscipline
  probabilisticSemantics_cert : probabilisticSemantics
  circuitSemantics_cert : circuitSemantics
  wilsonLoopSemantics_cert : wilsonLoopSemantics

namespace ThermodynamicGraphLambdaPacket

@[simp] theorem semanticInterpretation_holds (P : ThermodynamicGraphLambdaPacket) :
    P.semanticInterpretation :=
  P.semanticInterpretation_cert

@[simp] theorem linearResourceDiscipline_holds (P : ThermodynamicGraphLambdaPacket) :
    P.linearResourceDiscipline :=
  P.linearResourceDiscipline_cert

@[simp] theorem probabilisticSemantics_holds (P : ThermodynamicGraphLambdaPacket) :
    P.probabilisticSemantics :=
  P.probabilisticSemantics_cert

@[simp] theorem circuitSemantics_holds (P : ThermodynamicGraphLambdaPacket) :
    P.circuitSemantics :=
  P.circuitSemantics_cert

@[simp] theorem wilsonLoopSemantics_holds (P : ThermodynamicGraphLambdaPacket) :
    P.wilsonLoopSemantics :=
  P.wilsonLoopSemantics_cert

end ThermodynamicGraphLambdaPacket

end

/-! ## De Bruijn shift graph

The de Bruijn graph of order `n` over alphabet `α` has as vertices all words
of length `n`, and as edges the shift transitions: drop the first symbol and
append a new one.  This is mathematically distinct from de Bruijn *indices*
(which appear in `ThermoTerm` for nameless variable binding), but both
structures participate in the thermodynamic graph calculus:

- De Bruijn indices provide the *syntax* layer (nameless binding).
- De Bruijn graphs provide a *dynamics* layer (memory/shift state machine).

When the shift graph is decorated with forward/reverse rates, it becomes a
thermodynamic graph whose Wilson loops measure the irreversibility of the
shift dynamics. -/

section DeBruijnShiftGraph

variable (α : Type) [DecidableEq α]

/-- A word of length `n` over alphabet `α`, represented as `Fin n → α`. -/
def Word (n : ℕ) := Fin n → α

/-- The de Bruijn shift operation: drop the first symbol, shift left, append `a`.

`shift w a = (w₁, w₂, …, wₙ₋₁, a)` -/
def deBruijnShift {n : ℕ} (w : Word α (n + 1)) (a : α) : Word α (n + 1) :=
  fun i =>
    if h : i.val < n then w ⟨i.val + 1, by omega⟩
    else a

/-- A de Bruijn shift edge: source word, appended symbol, and target word. -/
structure DeBruijnEdge (n : ℕ) where
  source : Word α (n + 1)
  symbol : α
  target : Word α (n + 1)
  shift_law : target = deBruijnShift α source symbol

/-- Rate-decorated de Bruijn graph: each shift edge carries forward and reverse
transition rates, enabling thermodynamic analysis of memory/shift dynamics. -/
structure DecoratedDeBruijnGraph (n : ℕ) where
  forwardRate : DeBruijnEdge α n → ℝ
  reverseRate : DeBruijnEdge α n → ℝ

end DeBruijnShiftGraph

/-! ## Linear resource discipline

In pure λ-calculus, variables can be freely duplicated (contraction) and
discarded (weakening).  Thermodynamically, these operations have entropy cost:

- **Erasure** of one bit costs `kT ln 2` (Landauer's principle).
- **Duplication** requires a physical copying mechanism.

The linear resource discipline restricts `ThermoTerm` to use each variable
exactly once.  Nonlinear operations must be explicitly marked as
thermodynamic operations with associated entropy cost. -/

namespace ThermoTerm

/-- Count free-variable occurrences of de Bruijn index `k` in a term. -/
def freeVarCount (k : Nat) : ThermoTerm → Nat
  | db n => if n = k then 1 else 0
  | lam body => body.freeVarCount (k + 1)
  | app fn arg => fn.freeVarCount k + arg.freeVarCount k
  | nu body => body.freeVarCount (k + 1)
  | edge _ _ _ _ => 0
  | tensor l r => l.freeVarCount k + r.freeVarCount k
  | trace body => body.freeVarCount k

/-- A term satisfies the linear resource discipline if every free variable
is used exactly once.  This is checked at de Bruijn depth `d`. -/
def IsLinearAt (d : Nat) : ThermoTerm → Prop
  | db n => n < d
  | lam body => body.IsLinearAt (d + 1) ∧ body.freeVarCount d ≤ 1
  | app fn arg =>
      fn.IsLinearAt d ∧ arg.IsLinearAt d ∧
      ∀ k, k < d → fn.freeVarCount k + arg.freeVarCount k ≤ 1
  | nu body => body.IsLinearAt (d + 1) ∧ body.freeVarCount d ≤ 1
  | edge _ _ _ _ => ∀ k, k < d → (0 : Nat) ≤ 1
  | tensor l r =>
      l.IsLinearAt d ∧ r.IsLinearAt d ∧
      ∀ k, k < d → l.freeVarCount k + r.freeVarCount k ≤ 1
  | trace body => body.IsLinearAt d

/-- Top-level linear resource discipline. -/
def IsLinear (t : ThermoTerm) : Prop := t.IsLinearAt 0

/-- Thermodynamic cost of a nonlinear operation (erasure or duplication).
Measured in units of `kT`. -/
structure NonlinearCost where
  erasureCost : ℝ    -- Landauer bound: ≥ ln 2 per bit
  duplicationCost : ℝ
  erasure_nonneg : 0 ≤ erasureCost
  duplication_nonneg : 0 ≤ duplicationCost

/-! ### Operational semantics -/

/-- Shift de Bruijn indices at or above a cutoff.  Negative shifts are clipped
at `0`; well-scoped β-reductions use the standard shift/substitute/shift-down
pattern below. -/
def shiftAbove (d : Int) (cutoff : Nat) : ThermoTerm → ThermoTerm
  | db n => if n < cutoff then db n else db (Int.toNat (Int.ofNat n + d))
  | lam body => lam (shiftAbove d (cutoff + 1) body)
  | app fn arg => app (shiftAbove d cutoff fn) (shiftAbove d cutoff arg)
  | nu body => nu (shiftAbove d (cutoff + 1) body)
  | edge src dst forward reverse => edge src dst forward reverse
  | tensor left right => tensor (shiftAbove d cutoff left) (shiftAbove d cutoff right)
  | trace body => trace (shiftAbove d cutoff body)

/-- Shift all free de Bruijn indices. -/
def shift (d : Int) (t : ThermoTerm) : ThermoTerm :=
  shiftAbove d 0 t

/-- Capture-avoiding substitution for de Bruijn terms. -/
def subst (j : Nat) (s : ThermoTerm) : ThermoTerm → ThermoTerm
  | db n => if n = j then s else db n
  | lam body => lam (subst (j + 1) (shift (1 : Int) s) body)
  | app fn arg => app (subst j s fn) (subst j s arg)
  | nu body => nu (subst (j + 1) (shift (1 : Int) s) body)
  | edge src dst forward reverse => edge src dst forward reverse
  | tensor left right => tensor (subst j s left) (subst j s right)
  | trace body => trace (subst j s body)

/-- Top-level β-substitution for `(λ. body) arg`. -/
def substTop (arg body : ThermoTerm) : ThermoTerm :=
  shift (-1 : Int) (subst 0 (shift (1 : Int) arg) body)

/-- One-step operational semantics for the thermodynamic graph λ-calculus. -/
inductive Step : ThermoTerm → ThermoTerm → Prop
  | beta (body arg : ThermoTerm) :
      Step (app (lam body) arg) (substTop arg body)
  | app_left {fn fn' arg : ThermoTerm} :
      Step fn fn' → Step (app fn arg) (app fn' arg)
  | app_right {fn arg arg' : ThermoTerm} :
      Step arg arg' → Step (app fn arg) (app fn arg')
  | lam_body {body body' : ThermoTerm} :
      Step body body' → Step (lam body) (lam body')
  | nu_body {body body' : ThermoTerm} :
      Step body body' → Step (nu body) (nu body')
  | tensor_left {left left' right : ThermoTerm} :
      Step left left' → Step (tensor left right) (tensor left' right)
  | tensor_right {left right right' : ThermoTerm} :
      Step right right' → Step (tensor left right) (tensor left right')
  | trace_body {body body' : ThermoTerm} :
      Step body body' → Step (trace body) (trace body')

/-- Reflexive-transitive closure of the small-step semantics. -/
inductive Reduces : ThermoTerm → ThermoTerm → Prop
  | refl (t : ThermoTerm) : Reduces t t
  | tail {t u v : ThermoTerm} : Step t u → Reduces u v → Reduces t v

namespace Reduces

/-- A single operational step is a multi-step reduction. -/
theorem single {t u : ThermoTerm} (h : Step t u) : Reduces t u :=
  tail h (refl u)

end Reduces

/-- Normal forms are terms with no outgoing operational step. -/
def IsNormal (t : ThermoTerm) : Prop :=
  ¬ ∃ u, Step t u

end ThermoTerm

/-! ### Trace/port closure correctness -/

/-- Abstract port signature for graph terms. -/
structure PortSignature where
  openPort : Nat → Prop

namespace PortSignature

/-- A port signature is closed when no open port remains. -/
def IsClosed (S : PortSignature) : Prop :=
  ∀ p, ¬ S.openPort p

/-- All open ports, if any, are the distinguished port `p`. -/
def OnlyPort (S : PortSignature) (p : Nat) : Prop :=
  ∀ q, S.openPort q → q = p

/-- Closing a port removes that port from the open-port predicate. -/
def tracePort (S : PortSignature) (p : Nat) : PortSignature where
  openPort q := S.openPort q ∧ q ≠ p

/-- If `p` is the only possible open port, tracing/closing `p` leaves a closed
signature. -/
theorem tracePort_closed_of_onlyPort {S : PortSignature} {p : Nat}
    (h : S.OnlyPort p) :
    (S.tracePort p).IsClosed := by
  intro q hq
  exact hq.2 (h q hq.1)

end PortSignature

/-- Model-specific port interpretation for `ThermoTerm.trace`.

The operational syntax fixes `trace` as the binder/closure operator; a concrete
graph semantics supplies `portsOf` and proves that tracing a term removes the
distinguished port `0`. -/
structure TracePortSemantics where
  portsOf : ThermoTerm → PortSignature
  trace_ports : ∀ t, portsOf (ThermoTerm.trace t) = (portsOf t).tracePort 0

namespace TracePortSemantics

/-- Trace/port-closure correctness: if the body has no open port except the
distinguished trace port, then the traced term is port-closed. -/
theorem trace_portClosure_correct
    (S : TracePortSemantics)
    {t : ThermoTerm}
    (h : (S.portsOf t).OnlyPort 0) :
    (S.portsOf (ThermoTerm.trace t)).IsClosed := by
  rw [S.trace_ports t]
  exact PortSignature.tracePort_closed_of_onlyPort h

end TracePortSemantics

end InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus
