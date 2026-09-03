import DAG.LambdaReduction
import DAG.PHOASExpressionLayer
import DAG.TripleSystem
import Mathlib.Data.Set.Defs

/-!
# Proof-relevant topology for the de Bruijn lambda graph

This module is the typed graph/topology layer for the existing de Bruijn
LambdaTerm.  It does not replace the lambda syntax, the reduction relation,
the PHOAS lane, or the executable declaration DAG.

The important invariant is that a variable occurrence is never exported as a
bare natural number.  A binding edge carries the occurrence path, the selected
de Bruijn index, the complete binder stack, and a kernel-checked lookup witness.
An out-of-scope occurrence is retained as an unresolved vertex with the same
context rather than being silently discarded.

The syntax incidence relation is intentionally not declared acyclic: an
occurrence-to-binder edge points toward an enclosing binder, so the combined
syntax/binding graph is not the ranked causal DAG from the canonical layer.
Reduction paths are proof-relevant paths over the existing BetaStep relation.
-/

namespace DAG
namespace LambdaDeBruijnTopology

open InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge

/-- The existing de Bruijn term carrier. -/
abbrev Term :=
  InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge.LambdaTerm

/-- The existing proof-relevant beta-step relation. -/
abbrev BetaStep : Term → Term → Type :=
  InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge.LambdaTerm.BetaStep

/-- The existing propositional multi-step beta relation. -/
abbrev BetaStar : Term → Term → Prop :=
  InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge.LambdaTerm.BetaStar

/--
A path in a lambda syntax tree.

The path constructors preserve the parent path, so a graph export can identify
an occurrence or binder without assigning a fragile global node number.
Unresolved is a typed target for a variable occurrence with no binder in the
available stack.
-/
inductive LambdaPath : Type
  | root
  | absBody (parent : LambdaPath)
  | appLeft (parent : LambdaPath)
  | appRight (parent : LambdaPath)
  | unresolved (occurrence : LambdaPath)
  deriving DecidableEq, Repr

/-- Exact scope lookup for a de Bruijn index, including its binder stack. -/
def InScope (binderStack : List LambdaPath) (index : Nat) : Prop :=
  ∃ binder, binderStack.get? index = some binder

/--
A successful de Bruijn binding incidence.

The lookup proof is part of the edge payload.  Thus the graph never promotes a
natural-number index to a binding edge without kernel evidence for the
occurrence-to-binder connection.
-/
structure BindingWitness where
  occurrence : LambdaPath
  binder : LambdaPath
  index : Nat
  binderStack : List LambdaPath
  binder_lookup : binderStack.get? index = some binder

/-- An explicit unresolved occurrence; its failed lookup is retained. -/
structure UnboundWitness where
  occurrence : LambdaPath
  index : Nat
  binderStack : List LambdaPath
  unbound_lookup : binderStack.get? index = none

/-- Semantic edge kinds for the lambda incidence graph. -/
inductive LambdaEdgeKind
  | syntax
  | binding
  | unresolved
  deriving DecidableEq, Repr

/--
A graph edge over lambda paths.

Syntax edges point from a parent term node to a child term node.  Binding edges
follow the existing expression-export convention and point from the variable
occurrence to its binder.  Unresolved occurrences point to a dedicated
unresolved vertex, preserving malformed/open de Bruijn syntax for later audit.
-/
inductive LambdaGraphEdge : Type
  | absBody (parent : LambdaPath)
  | appLeft (parent : LambdaPath)
  | appRight (parent : LambdaPath)
  | bound (witness : BindingWitness)
  | unbound (witness : UnboundWitness)

namespace LambdaGraphEdge

/-- Source vertex of an incidence edge. -/
def source : LambdaGraphEdge → LambdaPath
  | .absBody parent => parent
  | .appLeft parent => parent
  | .appRight parent => parent
  | .bound witness => witness.occurrence
  | .unbound witness => witness.occurrence

/-- Target vertex of an incidence edge. -/
def target : LambdaGraphEdge → LambdaPath
  | .absBody parent => .absBody parent
  | .appLeft parent => .appLeft parent
  | .appRight parent => .appRight parent
  | .bound witness => witness.binder
  | .unbound witness => .unresolved witness.occurrence

/-- Semantic kind of an incidence edge. -/
def kind : LambdaGraphEdge → LambdaEdgeKind
  | .absBody _ => .syntax
  | .appLeft _ => .syntax
  | .appRight _ => .syntax
  | .bound _ => .binding
  | .unbound _ => .unresolved

@[simp] theorem source_absBody (parent : LambdaPath) :
    source (.absBody parent) = parent :=
  rfl

@[simp] theorem source_appLeft (parent : LambdaPath) :
    source (.appLeft parent) = parent :=
  rfl

@[simp] theorem source_appRight (parent : LambdaPath) :
    source (.appRight parent) = parent :=
  rfl

@[simp] theorem source_bound (witness : BindingWitness) :
    source (.bound witness) = witness.occurrence :=
  rfl

@[simp] theorem source_unbound (witness : UnboundWitness) :
    source (.unbound witness) = witness.occurrence :=
  rfl

@[simp] theorem target_absBody (parent : LambdaPath) :
    target (.absBody parent) = .absBody parent :=
  rfl

@[simp] theorem target_appLeft (parent : LambdaPath) :
    target (.appLeft parent) = .appLeft parent :=
  rfl

@[simp] theorem target_appRight (parent : LambdaPath) :
    target (.appRight parent) = .appRight parent :=
  rfl

@[simp] theorem target_bound (witness : BindingWitness) :
    target (.bound witness) = witness.binder :=
  rfl

@[simp] theorem target_unbound (witness : UnboundWitness) :
    target (.unbound witness) = .unresolved witness.occurrence :=
  rfl

@[simp] theorem kind_absBody (parent : LambdaPath) :
    kind (.absBody parent) = .syntax :=
  rfl

@[simp] theorem kind_appLeft (parent : LambdaPath) :
    kind (.appLeft parent) = .syntax :=
  rfl

@[simp] theorem kind_appRight (parent : LambdaPath) :
    kind (.appRight parent) = .syntax :=
  rfl

@[simp] theorem kind_bound (witness : BindingWitness) :
    kind (.bound witness) = .binding :=
  rfl

@[simp] theorem kind_unbound (witness : UnboundWitness) :
    kind (.unbound witness) = .unresolved :=
  rfl

/-- Read back the proof that a binding edge points to the selected binder. -/
theorem binding_lookup (witness : BindingWitness) :
    witness.binderStack.get? witness.index = some witness.binder :=
  witness.binder_lookup

/-- Read back the proof that an unresolved occurrence has no selected binder. -/
theorem unbound_lookup (witness : UnboundWitness) :
    witness.binderStack.get? witness.index = none :=
  witness.unbound_lookup

end LambdaGraphEdge

/--
The de Bruijn scope predicate on an explicit binder stack.

The stack is ordered with the innermost binder first, matching de Bruijn index
zero.  This predicate is separate from graph construction so malformed terms
can still be represented and audited.
-/
def wellScopedOn (binderStack : List LambdaPath) : Term → Prop
  | .var index => InScope binderStack index
  | .abs body => wellScopedOn (LambdaPath.root :: binderStack) body
  | .app fn arg => wellScopedOn binderStack fn ∧ wellScopedOn binderStack arg

/-- Closed/root-scoped de Bruijn terms. -/
def wellScoped (term : Term) : Prop :=
  wellScopedOn [] term

/--
The variable-level graph readout.

A successful list lookup produces a proof-carrying binding edge; a failed lookup
produces a proof-carrying unresolved edge.  No variable occurrence is omitted.
-/
def variableEdges
    (binderStack : List LambdaPath)
    (path : LambdaPath)
    (index : Nat) : List LambdaGraphEdge :=
  match h : binderStack.get? index with
  | some binder =>
      [LambdaGraphEdge.bound
        { occurrence := path
          binder := binder
          index := index
          binderStack := binderStack
          binder_lookup := h }]
  | none =>
      [LambdaGraphEdge.unbound
        { occurrence := path
          index := index
          binderStack := binderStack
          unbound_lookup := h }]

/--
Collect syntax and binding incidences from an existing LambdaTerm.

The binder stack is extended at an abstraction by the abstraction's own path.
This makes the target of index zero the nearest enclosing lambda node.
-/
def graphEdgesFrom
    (binderStack : List LambdaPath)
    (path : LambdaPath) : Term → List LambdaGraphEdge
  | .var index =>
      variableEdges binderStack path index
  | .abs body =>
      [LambdaGraphEdge.absBody path] ++
        graphEdgesFrom (path :: binderStack) (LambdaPath.absBody path) body
  | .app fn arg =>
      [LambdaGraphEdge.appLeft path] ++
        graphEdgesFrom binderStack (LambdaPath.appLeft path) fn ++
        [LambdaGraphEdge.appRight path] ++
        graphEdgesFrom binderStack (LambdaPath.appRight path) arg

/-- The complete finite incidence edge list for a term. -/
def graphEdges (term : Term) : List LambdaGraphEdge :=
  graphEdgesFrom [] LambdaPath.root term

/-- The finite vertex list induced by the collected incidence edges. -/
def graphVertices (term : Term) : List LambdaPath :=
  (graphEdges term).flatMap fun edge => [edge.source, edge.target]

/--
The universal incidence carrier for this lambda graph.

The relation object is the actual proof-relevant edge, not a lossy string or
bare de Bruijn index.
-/
def lambdaIncidenceSystem : DAG.TripleSystem where
  Obj := LambdaPath
  Rel := LambdaGraphEdge
  triple source edge target :=
    edge.source = source ∧ edge.target = target

/-- Every graph edge is a valid typed incidence triple. -/
theorem graphEdge_incidence (edge : LambdaGraphEdge) :
    lambdaIncidenceSystem.triple edge.source edge edge.target :=
  ⟨rfl, rfl⟩

/-- Every collected term edge has the same typed incidence guarantee. -/
theorem graphEdges_incidence (term : Term) :
    ∀ edge, edge ∈ graphEdges term →
      lambdaIncidenceSystem.triple edge.source edge edge.target := by
  intro edge _
  exact graphEdge_incidence edge

/-- Incoming relation cone over the typed lambda graph. -/
def incomingCone (term : Term) (target : LambdaPath) : Set LambdaPath :=
  {source | ∃ edge ∈ graphEdges term,
    edge.target = target ∧ edge.source = source}

/-- Read back the exact definition of the incoming cone. -/
theorem mem_incomingCone_iff
    (term : Term) (target source : LambdaPath) :
    source ∈ incomingCone term target ↔
      ∃ edge ∈ graphEdges term,
        edge.target = target ∧ edge.source = source :=
  Iff.rfl

/--
A proof-relevant path in the existing beta-reduction graph.

The middle list is retained, and the trace contains the kernel evidence for
each step.  This is the dynamic/topological lane; it is not identified with
the static syntax incidence graph.
-/
def ReductionPath (source target : Term) : Type :=
  Sigma fun middle : List Term =>
    DAG.ReductionTrace BetaStep source middle target

/-- Identity path in the reduction graph. -/
def reductionPathRefl (term : Term) : ReductionPath term term :=
  ⟨[], DAG.ReductionTrace.refl term⟩

/-- One proof-relevant beta edge as a reduction path. -/
def reductionPathSingle {source target : Term}
    (step : BetaStep source target) : ReductionPath source target :=
  ⟨[target], DAG.ReductionTrace.single step⟩

/-- Concatenation of two reduction paths. -/
noncomputable def composeReductionPath
    {source middle target : Term}
    (left : ReductionPath source middle)
    (right : ReductionPath middle target) : ReductionPath source target :=
  ⟨left.1 ++ right.1, DAG.ReductionTrace.trans left.2 right.2⟩

@[simp] theorem composeReductionPath_middle
    {source middle target : Term}
    (left : ReductionPath source middle)
    (right : ReductionPath middle target) :
    (composeReductionPath left right).1 = left.1 ++ right.1 :=
  rfl

/-- Every proof-relevant reduction path descends to the existing BetaStar relation. -/
theorem reductionPath_to_betaStar
    {source target : Term} (path : ReductionPath source target) :
    BetaStar source target :=
  InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge.LambdaTerm.betaTrace_to_betaStar
    path.1 path.2

/-- Composition of proof-relevant paths agrees with the existing beta relation. -/
theorem composeReductionPath_to_betaStar
    {source middle target : Term}
    (left : ReductionPath source middle)
    (right : ReductionPath middle target) :
    BetaStar source target :=
  InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge.LambdaTerm.betaStar_trans
    (reductionPath_to_betaStar left)
    (reductionPath_to_betaStar right)

/--
The PHOAS lane remains parallel to the de Bruijn lane.  This alias exposes the
existing carrier without asserting a de Bruijn-to-PHOAS translation that the
repository does not currently own.
-/
abbrev ScopedPHOAS (B F : Type) :=
  DAG.PHOASExpressionLayer.ScopedPHOASExpr B F

/-- PHOAS bound and free variables remain constructor-distinct. -/
theorem scopedPHOAS_bvar_ne_fvar
    {B F : Type} (bound : B) (free : F) :
    DAG.PHOASExpressionLayer.ScopedPHOASExpr.bvar bound ≠
      DAG.PHOASExpressionLayer.ScopedPHOASExpr.fvar free := by
  intro h
  cases h

end LambdaDeBruijnTopology
end DAG
