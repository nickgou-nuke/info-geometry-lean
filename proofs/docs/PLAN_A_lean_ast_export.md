# Plan A Revised: Export Lean's own AST (no tree-sitter needed)

Lean 4's compiler already has a full parser, elaborator, and environment.
We don't need tree-sitter — we can extract data directly from `Environment`.

## Why this is better

| | tree-sitter-lean4 | Lean Environment |
|---|---|---|
| Parse errors | ~10-20% of our files likely fail | 0 — uses the real parser |
| Type awareness | None | Full: knows `Matrix` vs `ℂ` vs `TensorProduct` |
| Dependency edges | Heuristic (grep `rw` args) | Exact: `Expr` contains direct references |
| Tactic extraction | Pattern match on names | `Syntax` nodes preserve tactic structure |
| Socket detection | `sorry` keyword search | `Expr.const` with `sorryAx` |
| Integration | External script | `lake build` with custom module |

## Architecture (revised)

```
proofs/*.lean
    │
    ▼
Lean 4 compiler (elan + lake) — already runs on `lake build`
    │  Environment.constants: name → (type, value, module, dependencies)
    │  Syntax trees: tactic structure, calc chains, rw arguments
    ▼
Lean metaprogram: `Elab.Command` that walks Environment
    │  - For each theorem: extract name, type, proof term
    │  - Resolve dependencies: which lemmas does this proof call?
    │  - Classify tactics: noncomm_ring, simp, rw, abel, ...
    │  - Detect sockets: `sorry` in proof term
    │  - Type classification: Matrix? TensorProduct? AlgEquiv?
    ▼
JSON export (one file: `proof_graph.json`)
    │
    ▼
ArangoDB ingestion (same as before)
```

## Step 1: Lean metaprogram for extraction

```lean
-- proofs/ASTExtractor.lean
import Lean
import Mathlib

open Lean Elab Command Meta

structure TheoremInfo where
  name : Name
  module : Name
  type : String
  status : String  -- "proved" | "socket"
  tactics : List String
  dependsOn : List Name
  line : Nat
  deriving ToJson, FromJson

elab "#extract_ast" : command => do
  let env ← getEnv
  let mut theorems : List TheoremInfo := []
  for (name, cinfo) in env.constants.toList do
    -- Filter: only from our modules
    if isOurModule env name then
      -- Get type and value
      let type := cinfo.type
      let value? := cinfo.value?
      -- Analyze proof term
      let tactics := extractTactics value?
      let deps := extractDependencies value?
      let status := if hasSorry value? then "socket" else "proved"
      theorems := { name, module, type, status, tactics, dependsOn } :: theorems
  -- Write JSON
  let json := toJson theorems
  IO.FS.writeFile "proof_graph.json" (pretty json)

-- Helper: check if constant is from our modules
def isOurModule (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some modIdx =>
      let modName := env.getModuleName modIdx
      "FibAnyonProofs" ∈ modName.components
  | none => false

-- Helper: extract tactics from Syntax
def extractTactics (value? : Option Expr) : List String :=
  match value? with
  | none => []
  | some v =>
      -- Walk the Expr tree, find `Syntax` nodes for tactics
      -- Tactics are identifiable by their `SyntaxNodeKind`
      ...
```

## Step 2: Dependency resolution

Lean's `Expr` already encodes dependencies. When you write `rw [e_sq]`,
the elaborator resolves `e_sq` to a `Name` reference in the environment.
We can extract these:

```lean
def extractDependencies (value? : Option Expr) : List Name :=
  match value? with
  | none => []
  | some v =>
      let deps := []
      -- Walk expr, collect all `Expr.const name` references
      -- that point to our modules
      for e in v do
        match e with
        | Expr.const name _ =>
            if isOurModule env name then
              deps := name :: deps
        | _ => pure ()
      deps.eraseDups
```

## Step 3: Type classification

```lean
def classifyType (type : Expr) : String :=
  -- Check if type involves Matrix, TensorProduct, AlgEquiv, etc.
  if type.containsConst ``Matrix then "matrix"
  else if type.containsConst ``TensorProduct then "tensor"
  else if type.containsConst ``AlgEquiv then "algebra"
  else if type.containsConst ``Submodule then "submodule"
  else "other"
```

## Step 4: Integration with lake build

Add to `lakefile.toml`:

```toml
[[lean_exe]]
name = "ASTExtractor"
root = "ASTExtractor"
```

Then:

```bash
lake build ASTExtractor
lake exe ASTExtractor > proof_graph.json
```

Or run as a custom command:

```bash
lake run extract-ast
```

## Step 5: GEPA optimization layer

Now GEPA works on Lean's own typed AST, not raw syntax:

```
JSON from Lean Environment
    │
    ▼
GEPA pass 1: Deduplication
    - Merge identical tactic sequences
    - Normalize `simp` argument lists
    │
    ▼
GEPA pass 2: Expansion
    - Inline lemma calls for depth analysis
    - Resolve calc chains into edge lists
    │
    ▼
GEPA pass 3: Classification
    - Tag theorems by proof style: "algebraic", "matrix_computation", "quotient_descent"
    - Tag tactics by risk: `ring` on `Matrix` → "likely noncomm_ring needed"
    │
    ▼
ArangoDB-ready JSON (enriched)
```

## Comparison: tree-sitter vs Lean Environment

| Metric | tree-sitter | Lean Env |
|--------|-------------|----------|
| Lines of new code | ~500 (Python) + grammar work | ~200 (Lean, already in build) |
| Parse correctness | ~80-90% | 100% (it's the compiler) |
| Type information | None | Full |
| Dependency edges | Best-effort | Exact |
| Build integration | External | `lake build` target |
| Maintenance | Need to sync grammar with Lean updates | Always in sync (uses same parser) |
