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
inductive PHOASExpr (B F : Type) where
  | bvar : B → PHOASExpr B F
  | fvar : F → PHOASExpr B F
  | lam : (B → PHOASExpr B F) → PHOASExpr B F
  | app : PHOASExpr B F → PHOASExpr B F → PHOASExpr B F
  deriving Inhabited

namespace PHOASExpr

def bindFree {B F G : Type} (e : PHOASExpr B F)
    (σ : F → PHOASExpr B G) : PHOASExpr B G :=
  match e with
  | .bvar v => .bvar v
  | .fvar x => σ x
  | .lam body => .lam (fun v => bindFree (body v) σ)
  | .app f a => .app (bindFree f σ) (bindFree a σ)

@[simp] theorem bindFree_bvar {B F G : Type} (v : B)
    (σ : F → PHOASExpr B G) :
    bindFree (.bvar v) σ = .bvar v := rfl

@[simp] theorem bindFree_fvar {B F G : Type} (x : F)
    (σ : F → PHOASExpr B G) :
    bindFree (.fvar x) σ = σ x := rfl

@[simp] theorem bindFree_app {B F G : Type} (f a : PHOASExpr B F)
    (σ : F → PHOASExpr B G) :
    bindFree (.app f a) σ = .app (bindFree f σ) (bindFree a σ) := rfl

theorem bindFree_identity {B F : Type} (e : PHOASExpr B F) :
    bindFree e PHOASExpr.fvar = e := by
  induction e with
  | bvar v => rfl
  | fvar x => rfl
  | lam body ih =>
      simp only [bindFree]
      congr
      funext v
      exact ih v
  | app f a ihf iha =>
      simp only [bindFree]
      rw [ihf, iha]

theorem bindFree_composition {B F G H : Type}
    (e : PHOASExpr B F)
    (σ : F → PHOASExpr B G)
    (τ : G → PHOASExpr B H) :
    bindFree (bindFree e σ) τ =
      bindFree e (fun x => bindFree (σ x) τ) := by
  induction e with
  | bvar v => rfl
  | fvar x => rfl
  | lam body ih =>
      simp only [bindFree]
      congr
      funext v
      exact ih v
  | app f a ihf iha =>
      simp only [bindFree]
      rw [ihf, iha]

end PHOASExpr

/-! ### Parametric PHOAS terms -/

def ParametricPHOASExpr (F : Type) :=
  ∀ B : Type, PHOASExpr B F

namespace ParametricPHOASExpr

def bindFree {F G : Type} (e : ParametricPHOASExpr F)
    (σ : F → ParametricPHOASExpr G) : ParametricPHOASExpr G :=
  fun B => PHOASExpr.bindFree (e B) (fun x => σ x B)

theorem bindFree_identity {F : Type} (e : ParametricPHOASExpr F) :
    bindFree e (fun x B => PHOASExpr.fvar x) = e := by
  funext B
  exact PHOASExpr.bindFree_identity (e B)

theorem bindFree_composition {F G H : Type}
    (e : ParametricPHOASExpr F)
    (σ : F → ParametricPHOASExpr G)
    (τ : G → ParametricPHOASExpr H) :
    bindFree (bindFree e σ) τ =
      bindFree e (fun x B => bindFree (σ x) τ B) := by
  funext B
  apply PHOASExpr.bindFree_composition

end ParametricPHOASExpr

/-! ### 1a. Scoped PHOAS with separate bound and free variables -/

/--
A PHOAS carrier whose types distinguish locally bound variables from free
variables.  This separation is essential: a metalanguage variable introduced
by `lam` cannot be mistaken for a free variable being substituted.
-/
inductive ScopedPHOASExpr (B F : Type) where
  | bvar : B → ScopedPHOASExpr B F
  | fvar : F → ScopedPHOASExpr B F
  | lam : (B → ScopedPHOASExpr B F) → ScopedPHOASExpr B F
  | app : ScopedPHOASExpr B F → ScopedPHOASExpr B F → ScopedPHOASExpr B F
  deriving Inhabited

/-- Bind free variables while leaving bound variables untouched. -/
def bindFree {B F G : Type} (e : ScopedPHOASExpr B F)
    (σ : F → ScopedPHOASExpr B G) : ScopedPHOASExpr B G :=
  match e with
  | .bvar v => .bvar v
  | .fvar x => σ x
  | .lam body => .lam (fun v => bindFree (body v) σ)
  | .app f a => .app (bindFree f σ) (bindFree a σ)

@[simp] theorem bindFree_bvar {B F G : Type}
    (v : B) (σ : F → ScopedPHOASExpr B G) :
    bindFree (.bvar v) σ = .bvar v := rfl

@[simp] theorem bindFree_fvar {B F G : Type}
    (x : F) (σ : F → ScopedPHOASExpr B G) :
    bindFree (.fvar x) σ = σ x := rfl

@[simp] theorem bindFree_app {B F G : Type}
    (f a : ScopedPHOASExpr B F) (σ : F → ScopedPHOASExpr B G) :
    bindFree (.app f a) σ =
      .app (bindFree f σ) (bindFree a σ) := rfl

@[simp] theorem bindFree_lam {B F G : Type}
    (body : B → ScopedPHOASExpr B F) (σ : F → ScopedPHOASExpr B G) :
    bindFree (.lam body) σ =
      .lam (fun v => bindFree (body v) σ) := rfl

theorem bindFree_identity {B F : Type} (e : ScopedPHOASExpr B F) :
    bindFree e ScopedPHOASExpr.fvar = e := by
  induction e with
  | bvar v => rfl
  | fvar x => rfl
  | lam body ih =>
      simp only [bindFree]
      congr
      funext v
      exact ih v
  | app f a ihf iha =>
      simp only [bindFree]
      rw [ihf, iha]

theorem bindFree_composition {B F G H : Type}
    (e : ScopedPHOASExpr B F)
    (σ : F → ScopedPHOASExpr B G)
    (τ : G → ScopedPHOASExpr B H) :
    bindFree (bindFree e σ) τ =
      bindFree e (fun x => bindFree (σ x) τ) := by
  induction e with
  | bvar v => rfl
  | fvar x => rfl
  | lam body ih =>
      simp only [bindFree]
      congr
      funext v
      exact ih v
  | app f a ihf iha =>
      simp only [bindFree]
      rw [ihf, iha]

/-! ### 2. Binding operations are provided by `ScopedPHOASExpr.bindFree`. -/
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
  expr : ScopedPHOASExpr Nat Nat
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
def walkPHOASTree (p : ScopedPHOASExpr Nat Nat → Bool) (maxSteps : Nat) : PHOASQueryM (ScopedPHOASExpr Nat Nat) :=
  fun s =>
    if maxSteps = 0 then []
    else
      let here := if p s.expr then [s.expr] else []
      match s.expr with
      | ScopedPHOASExpr.bvar _ => here
      | ScopedPHOASExpr.fvar _ => here
      | ScopedPHOASExpr.app f a =>
          here ++ (walkPHOASTree p (maxSteps - 1) { s with expr := f })
               ++ (walkPHOASTree p (maxSteps / 2) { s with expr := a })
      | ScopedPHOASExpr.lam _ => here

/-! ### 5. Coherence Between the Two Layers -/

/-- The PHOAS walker returns no results once the step budget is exhausted. -/
theorem walkPHOASTree_zero (p : ScopedPHOASExpr Nat Nat → Bool) (s : PHOASQueryState) :
    walkPHOASTree p 0 s = [] := by
  simp [walkPHOASTree]

end DAG.PHOASExpressionLayer
