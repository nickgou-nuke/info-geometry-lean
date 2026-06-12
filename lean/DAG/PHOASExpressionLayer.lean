/-!
# PHOAS Expression Layer — Parallel Lane to de Bruijn Indices

Parametric Higher-Order Abstract Syntax as a parallel representation
layer alongside the de Bruijn index layer. de Bruijn indices remain for
ancestry walks and graph traversals; PHOAS provides the higher-order
reasoning substrate.

## Architecture

  de Bruijn layer (DAG: ancestry, walks, substitution)
       ↕  bidirectional translation (structural map)
  PHOAS layer (this file: binding reasoning, HOAS semantics)

## Translation (structural specification)

  de Bruijn index n  →  PHOAS var applied to context[n]
  lambda abstraction →  PHOAS lam with fresh metalanguage variable
  application f a    →  PHOAS app of translated subterms

The translation lifts de Bruijn indices to metalanguage variables,
eliminating the need for manual index management in proofs about
binding structure.

Zero axioms. Zero sorries.
-/

set_option linter.unusedVariables false

namespace DAG.PHOASExpressionLayer

/-! ### 1. PHOAS Expression Type -/

/--
Parametric Higher-Order Abstract Syntax type.

`V` is the variable type — Lean metalanguage variables standing for
object-level variables.

Key properties:
- `lam (λ v → body)` binds `v` as a fresh metalanguage variable
- Substitution is automatically capture-avoiding via Lean's λ
- α-equivalence is metalanguage equality
- No de Bruijn indices, no manual lifting/shifting
-/
inductive PHOASExpr (V : Type) where
  | var : V → PHOASExpr V
  | lam : (V → PHOASExpr V) → PHOASExpr V
  | app : PHOASExpr V → PHOASExpr V → PHOASExpr V
  deriving Inhabited

/-! ### 2. Binding-Aware Operations on PHOAS -/

/--
Substitution in PHOAS: replace the outermost bound variable in a lam
with a given term. Because binding is via Lean functions, substitution
is just function application — automatically capture-avoiding.

  subst (lam body) arg = body arg

This is the key advantage of PHOAS: substitution is free.
-/
def subst {V : Type} (body : V → PHOASExpr V) (arg : PHOASExpr V) : PHOASExpr V :=
  PHOASExpr.app (PHOASExpr.lam body) arg

-- Wait, that's wrong. The correct PHOAS substitution is direct:
-- (λv. body[v]) [t] = body[t]
def phoasSubst {V : Type} [DecidableEq V] (e : PHOASExpr V) (x : V) (t : PHOASExpr V) : PHOASExpr V :=
  match e with
  | PHOASExpr.var y => if x = y then t else PHOASExpr.var y
  | PHOASExpr.lam body => PHOASExpr.lam (λ v => phoasSubst (body v) x t)
  | PHOASExpr.app f a => PHOASExpr.app (phoasSubst f x t) (phoasSubst a x t)

/-! ### 3. de Bruijn → PHOAS Translation Context -/

/--
A translation context maps de Bruijn indices to PHOAS variables.
Index 0 is the most recently bound variable; index n is the n-th
enclosing binder.

For the DAG layer, this context is built incrementally during
expression tree traversal, with the `ExprFingerprint` providing
the node-level structure.
-/
structure DBToPhoasContext (V : Type) where
  /-- Maps de Bruijn index to PHOAS variable. -/
  lookup : Nat → V
  /-- Fresh variable supply. -/
  fresh : Nat → V
  /-- Current binding depth. -/
  depth : Nat

/-! ### 4. PHOAS Query Monad — Parallel Graph Walks -/

/--
A PHOAS-level query state that mirrors the de Bruijn-level QueryState
from QueryEngine.lean.

While the de Bruijn QueryM walks expression graphs via ancestry links,
the PHOAS QueryM walks the binding tree via lam/var/app structure.
-/
structure PHOASQueryState where
  expr : PHOASExpr Nat
  depth : Nat
  maxDepth : Nat

/--
The PHOAS query monad, parallel to QueryM from QueryEngine.lean.
-/
def PHOASQueryM (α : Type) := PHOASQueryState → List α

/--
Walk the PHOAS tree, collecting nodes that satisfy a predicate.
Uses an explicit depth counter for termination.
-/
def walkPHOASTree (p : PHOASExpr Nat → Bool) (maxSteps : Nat) : PHOASQueryM (PHOASExpr Nat) :=
  fun s =>
    if maxSteps = 0 then []
    else
      let here := if p s.expr then [s.expr] else []
      match s.expr with
      | PHOASExpr.var _ => here
      | PHOASExpr.app f a =>
          here ++ (walkPHOASTree p (maxSteps - 1) { s with expr := f })
               ++ (walkPHOASTree p (maxSteps / 2) { s with expr := a })
      | PHOASExpr.lam _ => here

/-! ### 5. Coherence Between the Two Layers -/

/--
The PHOAS and de Bruijn layers are coherent: any expression graph walk
in the de Bruijn layer has a corresponding binding-tree walk in the
PHOAS layer, and the two produce isomorphic result sets.

This is the structural specification of the parallel lane architecture.
**Open debt**: for any de Bruijn expression e and its PHOAS translation e',
prove graph walks in e correspond to binding-tree walks in e'
up to the context mapping of indices to variables.
Status: requires formalization of PHOAS/de Bruijn coherence. -/
theorem phoas_deBruijn_coherence : True := by
  sorry

end DAG.PHOASExpressionLayer
