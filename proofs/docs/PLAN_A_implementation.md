# Plan A Implementation: GEPA-optimized tree-sitter-lean4 → ArangoDB

## Baseline: what tree-sitter-lean4 covers

From `wvhulle/tree-sitter-lean` (crate: `tree-sitter-lean4` v0.1.1):

Covered:
- `def`, `theorem`, `lemma`, `example`
- `import`, `open`, `namespace`, `end`
- `calc`, `rw`, `simp`, `apply`, `exact`, `refine`
- `have`, `let`, `match`, `fun`
- `∀`, `→`, `:=`, `|>`, `∘`
- `structure`, `inductive`, `class`, `instance`
- `#check`, `#eval`
- Basic term syntax: `(a b : α) → β`, `fun x => ...`

Likely gaps (what we use heavily):
- `noncomm_ring` tactic — may be parsed as generic identifier
- `TensorProduct` notation: `a ⊗ₜ[R] b`
- `Submodule` syntax: `R ≤ Submodule.comap f R`
- `AlgEquiv` types: `≃ₐ[ℂ]`
- `LinearMap` composition: `f ∘ₗ g`
- `Units` / `ˣ` notation
- Unicode: `σ⁺`, `σ⁻`, `σ₃`, `P₊`, `P₋`
- `set_option` blocks
- `noncomputable section`
- Complex `calc` chains with mixed `:=` and `by` blocks

## Phase 1: Gap detection (1 hour)

```bash
# Clone and build the grammar
git clone https://github.com/wvhulle/tree-sitter-lean
cd tree-sitter-lean
nix build   # or: cargo build

# Parse all .lean files, collect errors
for f in proofs/*.lean; do
  tree-sitter parse "$f" 2>&1 | grep -E "ERROR|MISSING" >> parse_errors.txt
done
```

Output: list of `(file, line, column, expected node type)` for each parse failure.

## Phase 2: GEPA grammar optimization (2-3 hours)

GEPA operates on the tree-sitter grammar as a graph:

```
Grammar rules (grammar.js)
    │
    ▼
GEPA analysis pass
    - Parse error → missing rule in grammar
    - Partial parse → incomplete rule (doesn't cover all syntax)
    - Ambiguity → conflicting rules (GEPA chooses based on precedence)
    │
    ▼
GEPA extension pass
    - For each parse failure, suggest grammar rule additions
    - For each incomplete rule, suggest extensions
    - Normalize Unicode alternatives (σ⁺ vs sigma_plus)
    │
    ▼
Optimized grammar.js
```

Concrete example: `noncomm_ring` is not in the grammar.

```javascript
// Current grammar (simplified)
tactic: $ => choice(
  $.exact,
  $.apply,
  $.rw,
  $.simp,
  ...
)

// GEPA-extended grammar
tactic: $ => choice(
  $.exact,
  $.apply,
  $.rw,
  $.simp,
  $.noncomm_ring,    // ← added
  $.abel,            // ← added
  $.field_simp,      // ← added
  $.norm_num,        // ← added
  ...
)
```

GEPA can do this automatically by scanning `parse_errors.txt` and matching
unrecognized identifiers against known Lean 4 tactic names from the mathlib
tactic registry.

## Phase 3: AST extraction schema (1 hour)

For each successfully parsed `.lean` file, tree-sitter produces a CST.
We need to extract specific node types into our JSON schema:

```javascript
// tree-sitter query (S-expression syntax)
// queries/extract.scm

(module
  (command (import . (identifier) @import_name)) @import

(module
  (command (declaration
    name: (identifier) @theorem_name
    type: (term) @theorem_type
    value: (term) @theorem_proof)) @theorem

(module
  (command (declaration
    name: (identifier) @structure_name
    (structure_body) @structure_body)) @structure

(tactic_explicit
  (identifier) @tactic_name) @tactic
```

Python script `extract.py` applies these queries and builds clean JSON.

## Phase 4: ArangoDB ingestion (1 hour)

```python
# scripts/ingest.py
from arango import ArangoClient
import json

client = ArangoClient(hosts="http://localhost:8529")
db = client.db("lean_proofs")

# Create collections
db.create_collection("modules")
db.create_collection("theorems")
db.create_collection("tactics")
db.create_collection("sockets")
db.create_graph("proof_graph",
    edge_definitions=[
        {"edge_collection": "imports", "from": ["modules"], "to": ["modules"]},
        {"edge_collection": "depends_on", "from": ["theorems"], "to": ["theorems"]},
        {"edge_collection": "uses_tactic", "from": ["theorems"], "to": ["tactics"]},
    ]
)

# Ingest
for module_file in glob("proofs/*.lean"):
    ast = parse_and_extract(module_file)
    db.collection("modules").insert(ast.module)
    for t in ast.theorems:
        db.collection("theorems").insert(t)
    for e in ast.edges:
        db.collection(e.type).insert(e)
```

## Phase 5: Query layer (30 min)

Same AQL queries as Plan A, now running against real data:

```aql
// Anti-pattern: `ring` on non-commutative types
FOR t IN theorems
  FOR tactic IN t.tactics
    FILTER tactic.name == "ring"
    FOR m IN 1..1 INBOUND t depends_on
      FILTER CONTAINS(LOWER(m.name), "matrix")
          OR CONTAINS(LOWER(m.name), "tensor")
    RETURN {
      theorem: t.name,
      module: t.module,
      imported_matrix_module: m.name
    }

// Dependency depth of a theorem
FOR v, e IN 1..10 OUTBOUND "theorems/ChiralTensorRecoupling.e_sq" depends_on
  COLLECT depth = LENGTH(e.paths[0].edges) INTO group
  RETURN { depth, count: COUNT(group) }

// Find the most-depended-on lemmas
FOR t IN theorems
  LET deps = LENGTH(FOR d IN depends_on FILTER d._to == t._id RETURN 1)
  SORT deps DESC
  LIMIT 10
  RETURN { name: t._key, used_by: deps }
```

## Deliverables

```
proofs/
├── scripts/
│   ├── parse_all.sh          # Run tree-sitter on all .lean files
│   ├── extract.py            # tree-sitter query → JSON extraction
│   ├── ingest.py             # JSON → ArangoDB
│   └── query.py              # Pre-built AQL queries
├── grammar/
│   ├── tree-sitter-lean/     # (submodule) base grammar
│   └── gepa-patches/         # Grammar extensions for our dialect
└── docs/
    └── PLAN_A_implementation.md
```

## Time estimate

| Phase | Time |
|-------|------|
| Gap detection | 1h |
| GEPA grammar extension | 2-3h |
| AST extraction | 1h |
| ArangoDB ingestion | 1h |
| Query layer | 30min |
| **Total** | **5-7h** |
