# Plan B: Self-hosted Lean 4 metaprogramming (GEPA + ArangoDB)

Extend `lean4-tree-sitter` with the Lean 4 grammar, write Lean metaprograms
that extract proof structure with type awareness, ingest into ArangoDB.

## Architecture

```
proofs/*.lean
    │
    ▼
lean4-tree-sitter (Lean 4 + vendored tree-sitter-lean4 grammar)
    │  - Typed CST nodes with source maps
    │  - Declaration extraction (name, type, proof term)
    │  - Type-aware: can distinguish `ring` on ℂ vs `ring` on Matrix
    ▼
GEPA (Graph Expansion for Proof Analysis)
    │  - Inlines imports: expand `e_sq` to full dependency tree
    │  - Tactic normalization: `simp [add_tmul, tmul_add]` → `simp` + arguments
    │  - Socket detection: `structure ... where` with all-Prop fields
    │  - Proof size metrics: lines, tactics, depth
    ▼
ArangoDB graph (same schema as Plan A, richer data)
    │
    ▼
AQL queries + Lean metaprograms for feedback loop
```

## Step 1: Add Lean 4 grammar to lean4-tree-sitter

The `lean4-tree-sitter` package at `predictable-machines/lean4-tree-sitter`
vendors grammars in `vendor/`. Currently: Java, Python, Kotlin.

Add:

```bash
# In lean4-tree-sitter repo:
mkdir vendor/tree-sitter-lean4
cp -r tree-sitter-lean4/src vendor/tree-sitter-lean4/
# tree-sitter-lean4 grammar.js, scanner.c, etc.
```

Then register the grammar in `Lean4TreeSitter.lean`:

```lean
def Lean4Grammar : Grammar where
  name := "lean4"
  scannerPath := "vendor/tree-sitter-lean4/scanner.c"
  grammarPath := "vendor/tree-sitter-lean4/grammar.js"
```

Now `lean4-tree-sitter` can parse `.lean` files and produce typed Lean 4 CST nodes.

## Step 2: Declaration extraction (type-aware)

Unlike Plan A (pure syntax), Plan B has access to the Lean typechecker.
This means we can:

- Resolve imports: `ChiralTensorRecoupling.e_sq` actually refers to theorem at line 220
- Type-aware tactic classification: `ring` on `Matrix (Fin 8) (Fin 8) ℂ` → "non-commutative ring, likely to fail"
- Socket detection: a `structure` where all fields are `Prop` and none are proved is a socket
- Dependency resolution: `e_sq` uses `X_mul_X`, `Y_mul_Y`, etc. — trace through `rw` arguments

```lean
-- Lean metaprogram that extracts theorem metadata
open Lean Elab Meta

def extractTheorems (moduleName : Name) : MetaM (List TheoremInfo) := do
  let env ← getEnv
  let modIdx := env.getModuleIdx? moduleName
  -- walk constants in the module
  -- for each `theorem` / `def`:
  --   get name, type, value (proof term)
  --   count tactics in proof term
  --   resolve `rw` / `simp` argument references
  ...
```

## Step 3: GEPA integration

GEPA (Graph Expansion for Proof Analysis) operates on the typed AST:

```
Raw CST from tree-sitter
    │
    ▼
GEPA pass 1: Resolution
    - Replace import aliases with canonical names
    - Resolve `rw [h]` → `rw [X_mul_X]` by looking up `h` in context
    │
    ▼
GEPA pass 2: Expansion
    - Inline lemma bodies for depth analysis
    - Normalize tactics to canonical forms
    - Flatten `calc` chains into dependency edges
    │
    ▼
GEPA pass 3: Optimization
    - Prune unused lemmas from dependency graph
    - Merge identical subproofs
    - Detect redundant `simp` arguments
    │
    ▼
ArangoDB-ready JSON
```

## Step 4: Lean → ArangoDB bridge

```lean
def ingestToArangoDB (data : ProofGraph) : IO Unit := do
  -- Use ArangoDB HTTP API
  -- POST /_api/document/theorems for each theorem
  -- POST /_api/edges/depends_on for each dependency
  ...
```

This runs as a `lake` task:

```bash
lake run ingest-proofs -- modules=ChiralCausalCone,ChiralTensorRecoupling,...
```

## Step 5: Feedback loop

Once the data is in ArangoDB, we can query it FROM Lean:

```lean
def suggestTactic (goal : MVarId) : MetaM (List TacticHint) := do
  -- Query ArangoDB: "what tactics succeeded on similar goals?"
  -- Similarity: goal type, hypotheses, module context
  let query := "FOR t IN theorems
    FILTER t.module IN @context
    AND t.tactics INCLUDES @preferred
    RETURN t"
  ...
```

And use it as a `#suggest` command:

```lean
#suggest "prove e_matrix_sq using bridge"
-- ArangoDB query: "proofs involving `AlgEquiv` + `kronecker` + `e_sq`"
-- Returns: use `congrArg bridge e_sq` then `simpa`
```

## Comparison: Plan A vs Plan B

| | Plan A | Plan B |
|---|---|---|
| **Time to first result** | 1-2 days | 1-2 weeks |
| **Parser** | tree-sitter-lean4 (Rust) | lean4-tree-sitter (Lean 4 + vendored grammar) |
| **Type awareness** | No (syntax only) | Yes (Lean typechecker) |
| **Tactic resolution** | Pattern match on names | Resolve `rw` args to actual lemmas |
| **Dependency graph** | Coarse (import-based) | Fine (tactic-level) |
| **Maintenance** | External script | `lake` integrated |
| **Query from Lean** | No | Yes (`#suggest`, `#query`) |

## Recommended: A → B

Start with Plan A to get the ingestion pipeline working and queries
answering real questions (which took us 6+ hours of manual grepping).
Then extend to Plan B for type-aware enrichment and the Lean metaprogramming
feedback loop.
