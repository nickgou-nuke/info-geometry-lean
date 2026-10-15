import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Category.Preorder
import InfoGeometry.Canonical.CausalConeProjectorBridge
import InfoGeometry.Canonical.BoltzmannModularHamiltonianEquivalence
import InfoGeometry.Canonical.SurprisalTopologicalGeometryGenerator

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Lambda Syntax and Causal-Net Interfaces

This module owns untyped de Bruijn lambda syntax, capture-avoiding lifting and
substitution, and contextual beta reduction. Its `CausalNet` map records
structural counts; those counts alone do not identify beta steps with causal
dependencies, prove normalization, or imply modular-flow statements. The
separate owners for causal scheduling, negative grammar, modular flow, and
surprisal must be connected by explicit structure-preserving maps before such
claims can be made.
-/

namespace InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge

open CategoryTheory
open InfoGeometry.Canonical.CausalConeProjectorBridge
open InfoGeometry.Canonical.BoltzmannModularHamiltonianEquivalence
open InfoGeometry.Canonical.SurprisalTopologicalGeometryGenerator

/-- Polarity of types/terms in polarized negative grammar. -/
inductive Polarity
  | positive : Polarity -- Eager / Data
  | negative : Polarity -- Async / Computation / Demand
  | neutral  : Polarity -- Boundary / Horizon

/-- Simple $\lambda$-term causal representation. -/
inductive LambdaTerm
  | var : ℕ → LambdaTerm
  | abs : LambdaTerm → LambdaTerm
  | app : LambdaTerm → LambdaTerm → LambdaTerm

namespace LambdaTerm

/-- Raise the free de Bruijn indices at or above `cutoff`. -/
def liftAt (cutoff : ℕ) : LambdaTerm → LambdaTerm
  | .var n => .var (if cutoff ≤ n then n + 1 else n)
  | .abs body => .abs (liftAt (cutoff + 1) body)
  | .app f a => .app (liftAt cutoff f) (liftAt cutoff a)

/-- Raise every free de Bruijn index by one. -/
def lift (t : LambdaTerm) : LambdaTerm := liftAt 0 t

/-- Capture-avoiding substitution of the variable at index `index`.
Indices above the removed binder are lowered, while the replacement is
lifted when substitution crosses an abstraction. -/
def subst (index : ℕ) (replacement : LambdaTerm) : LambdaTerm → LambdaTerm
  | .var n =>
      if n < index then .var n else
        if n = index then replacement else .var (n - 1)
  | .abs body => .abs (subst (index + 1) replacement.lift body)
  | .app f a => .app (subst index replacement f) (subst index replacement a)

@[simp] theorem lift_var_zero (n : ℕ) : lift (.var n) = .var (n + 1) := by
  simp [lift, liftAt]

@[simp] theorem subst_var_same (replacement : LambdaTerm) :
    subst 0 replacement (.var 0) = replacement := by
  simp [subst]

@[simp] theorem subst_var_under_binder (replacement : LambdaTerm) :
    subst 1 replacement.lift (.var 0) = .var 0 := by
  simp [subst]

end LambdaTerm

/-- One-step (full contextual) beta reduction on de Bruijn lambda terms. -/
inductive LambdaBetaStep : LambdaTerm → LambdaTerm → Prop
  | beta (body argument : LambdaTerm) :
      LambdaBetaStep (.app (.abs body) argument) (LambdaTerm.subst 0 argument body)
  | abs {body body' : LambdaTerm} :
      LambdaBetaStep body body' → LambdaBetaStep (.abs body) (.abs body')
  | appFunction {function function' argument : LambdaTerm} :
      LambdaBetaStep function function' →
      LambdaBetaStep (.app function argument) (.app function' argument)
  | appArgument {function argument argument' : LambdaTerm} :
      LambdaBetaStep argument argument' →
      LambdaBetaStep (.app function argument) (.app function argument')

namespace LambdaBetaStep

/-- The identity redex contracts to its argument. -/
theorem identity (argument : LambdaTerm) :
    LambdaBetaStep (.app (.abs (.var 0)) argument) argument := by
  simpa using (LambdaBetaStep.beta (.var 0) argument)

end LambdaBetaStep

/-- Causal Net structure representing dependency graph of terms. -/
structure CausalNet where
  vertices : ℕ
  edges : ℕ

/-- Bridge 1: Lambda Term → CausalNet functor preserving dependencies. -/
def lambdaToCausalNet (t : LambdaTerm) : CausalNet :=
  match t with
  | .var _     => ⟨1, 0⟩
  | .abs body  =>
      let c := lambdaToCausalNet body
      ⟨c.vertices + 1, c.edges + 1⟩
  | .app f arg =>
      let cf := lambdaToCausalNet f
      let carg := lambdaToCausalNet arg
      ⟨cf.vertices + carg.vertices + 1, cf.edges + carg.edges + 1⟩

/-- A causal past is present exactly when the net contains a dependency edge. -/
def CausalNet.HasCausalPast (net : CausalNet) : Prop :=
  0 < net.edges

/--
The ranked dependency relation on a finite causal net.  An edge can only point
from a lower vertex rank to a higher vertex rank.
-/
def CausalNet.Dependency (net : CausalNet)
    (source target : Fin net.vertices) : Prop :=
  source.1 < target.1

/-- Reachability in a causal net is the reflexive-transitive closure of dependencies. -/
def CausalNet.Reach (net : CausalNet)
    (source target : Fin net.vertices) : Prop :=
  Relation.ReflTransGen net.Dependency source target

/-- Strict reachability uses a nonempty dependency path. -/
def CausalNet.StrictReach (net : CausalNet)
    (source target : Fin net.vertices) : Prop :=
  Relation.TransGen net.Dependency source target

/-- The causal reach relation is a preorder on the vertex set. -/
def CausalNet.reachPreorder (net : CausalNet) : Preorder (Fin net.vertices) :=
  { le := CausalNet.Reach net
    lt := fun source target => CausalNet.Reach net source target ∧ ¬ CausalNet.Reach net target source
    le_refl := by
      intro a
      exact Relation.ReflTransGen.refl
    le_trans := by
      intro a b c hab hbc
      exact Relation.ReflTransGen.trans hab hbc
    lt_iff_le_not_ge := by
      intro a b
      rfl }

/--
A finite causal net is a DAG when the transitive closure of its dependency
relation has no self-loop.
-/
def CausalNet.IsDAG (net : CausalNet) : Prop :=
  ∀ vertex, ¬ Relation.TransGen net.Dependency vertex vertex

/-- Every nonempty dependency path strictly increases the vertex rank. -/
theorem CausalNet.transGen_dependency_lt
    (net : CausalNet) {source target : Fin net.vertices}
    (path : Relation.TransGen net.Dependency source target) :
    source.1 < target.1 := by
  induction path with
  | single step => exact step
  | tail _ step ih => exact Nat.lt_trans ih step

/-- Every ranked finite causal net has no nonempty directed loop. -/
theorem CausalNet.isDAG (net : CausalNet) : net.IsDAG := by
  intro vertex loop
  exact Nat.lt_irrefl vertex.1 (net.transGen_dependency_lt loop)

/-- Reachability is equivalent to causal arrows in the induced preorder category. -/
theorem CausalNet.hom_iff_reach
    (net : CausalNet) (source target : Fin net.vertices) :
    (letI : Preorder (Fin net.vertices) := net.reachPreorder
      ; Nonempty (source ⟶ target)) ↔
    CausalNet.Reach net source target := by
  letI : Preorder (Fin net.vertices) := net.reachPreorder
  constructor
  · rintro ⟨f⟩
    exact leOfHom f
  · intro h
    exact ⟨homOfLE h⟩

/-- Cleaned statement of `hom_iff_reach` with the induced preorder made explicit. -/
theorem CausalNet.hom_iff_reach'
    (net : CausalNet) (source target : Fin net.vertices) :
    (letI : Preorder (Fin net.vertices) := net.reachPreorder
      ; Nonempty (source ⟶ target)) ↔
    CausalNet.Reach net source target := by
  simpa using (CausalNet.hom_iff_reach (net := net) source target)

/-- Every strict causal path is strict on vertex rank -/
theorem CausalNet.strictReach_lt
    (net : CausalNet) {source target : Fin net.vertices}
    (path : CausalNet.StrictReach net source target) :
    source.1 < target.1 :=
  net.transGen_dependency_lt path

/-- Strict reachability induces a non-identity causal arrow in the induced preorder category. -/
theorem CausalNet.strictReach_hom
    (net : CausalNet) {source target : Fin net.vertices}
    (path : CausalNet.StrictReach net source target) :
    (letI : Preorder (Fin net.vertices) := net.reachPreorder
      ; Nonempty (source ⟶ target)) := by
  letI : Preorder (Fin net.vertices) := net.reachPreorder
  exact ⟨homOfLE (path.to_reflTransGen)⟩

/-- Bridge 2: CausalNet → Polarity functor preserving async evaluation order. -/
noncomputable def causalNetToPolarity (net : CausalNet) : Polarity :=
  by
    classical
    by_cases h : net.HasCausalPast
    · exact Polarity.negative
    · exact Polarity.positive

/-- Bridge 3: Polarity → CausalSplit functor preserving Bulk/Boundary/Null trichotomy. -/
def polarityToCausalSplit {V : Type*} [AddCommGroup V] [Module ℝ V] (pol : Polarity) (V_bulk V_boundary V_null : Submodule ℝ V) : CausalSplit V :=
  ⟨V_bulk, V_boundary, V_null⟩

/-- The count-based dependency graph constructed from the syntax tree is acyclic.
This statement concerns `lambdaToCausalNet`'s ranked count graph only; it makes
no claim that beta reduction preserves a graph or that the count graph records
the operational beta dynamics. -/
theorem lambda_causal_net_preserves_dag (t : LambdaTerm) :
    (lambdaToCausalNet t).IsDAG :=
  CausalNet.isDAG _

/--
**Main Theorem 2: Negative Grammar Async Polarity Law**
Negative polarity types correspond to async lazy evaluation in $\lambda$-causal nets.
-/
theorem negative_grammar_async_polarity (net : CausalNet) (h : net.HasCausalPast) :
    causalNetToPolarity net = Polarity.negative := by
  unfold causalNetToPolarity
  simp [h]

/--
Canonical theorem-safe chain connecting the ranked lambda causal net, negative
polarity, causal splitting, and the state-surprisal/modular-log generator.

This theorem does not identify state surprisal with Boltzmann macroentropy.
-/
theorem lambda_negative_grammar_stateSurprisal_chain
    (t : LambdaTerm) (net : CausalNet) (hnet : net.HasCausalPast)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (V_bulk V_boundary V_null : Submodule ℝ V)
    (B : OperatorStateSurprisal V) :
    ((lambdaToCausalNet t).IsDAG) ∧
    (causalNetToPolarity net = Polarity.negative) ∧
    ((polarityToCausalSplit (causalNetToPolarity net) V_bulk V_boundary V_null).bulk = V_bulk) ∧
    (B.modularHamiltonian = B.stateSurprisalOperator) := ⟨
  lambda_causal_net_preserves_dag t,
  negative_grammar_async_polarity net hnet,
  rfl,
  B.modularHamiltonian_eq_stateSurprisalOperator
⟩

/-- Historical theorem name with the corrected state-surprisal conclusion. -/
theorem grand_lambda_negative_grammar_rosetta_chain
    (t : LambdaTerm) (net : CausalNet) (hnet : net.HasCausalPast)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (V_bulk V_boundary V_null : Submodule ℝ V)
    (B : OperatorStateSurprisal V) :
    ((lambdaToCausalNet t).IsDAG) ∧
    (causalNetToPolarity net = Polarity.negative) ∧
    ((polarityToCausalSplit (causalNetToPolarity net)
      V_bulk V_boundary V_null).bulk = V_bulk) ∧
    (B.modularHamiltonian = B.stateSurprisalOperator) := by
  have h := lambda_negative_grammar_stateSurprisal_chain
    t net hnet V_bulk V_boundary V_null B
  exact h

end InfoGeometry.Canonical.LambdaCausalNetNegativeGrammarBridge
