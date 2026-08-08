# Plan A: External AST pipeline (Python/Rust → ArangoDB)

Parse `proofs/` with `tree-sitter-lean4`, extract proof structure,
ingest into ArangoDB, query with AQL.

## Architecture

```
proofs/*.lean
    │
    ▼
tree-sitter-lean4 (Rust, via Python binding or CLI)
    │  CST nodes: module, theorem, tactic, import, calc, rw, ...
    ▼
JSON AST dump (one file per .lean module)
    │
    ▼
Python ingestion script
    │  - theorem → node with name, file, line, status (proved/socket)
    │  - import → edge (module A → module B)
    │  - tactic → edge (theorem → tactic: noncomm_ring, simp, ...)
    ▼
ArangoDB graph
    │
    ▼
AQL queries
    - "find all proofs using `ring` on matrix types"
    - "dependency graph: what does e_sq depend on?"
    - "all sockets (structures with only Prop fields)"
    - "tactic usage stats across 200 modules"
```

## Step 1: Parse with tree-sitter-lean4

```bash
cargo install tree-sitter-cli
# Or use the Python binding:
pip install tree-sitter tree-sitter-lean4
```

Walk `proofs/` directory, parse each `.lean` file, extract:

| Node type | Extract | Edge |
|-----------|---------|------|
| `module` | name, file path | — |
| `theorem` / `def` | name, signature, proof body | module → theorem |
| `import` | module name | theorem → imported module |
| `sorry` | location | theorem → socket marker |
| `calc` block | steps | theorem → calc structure |
| `rw` / `simp` / `noncomm_ring` / ... | tactic name, args | theorem → tactic |
| `#check` | expression | module → checked item |
| `structure` | name, fields | module → structure |
| `abbrev` | name, expansion | module → abbrev |

## Step 2: JSON schema for ingestion

```json
{
  "modules": [
    {
      "_key": "ChiralTensorRecoupling",
      "path": "proofs/ChiralTensorRecoupling.lean",
      "lines": 448,
      "theorems": ["e_sq", "projector_tensor_identity", ...],
      "imports": ["Mathlib", "ChiralCausalCone"]
    }
  ],
  "theorems": [
    {
      "_key": "ChiralTensorRecoupling.e_sq",
      "module": "ChiralTensorRecoupling",
      "status": "proved",
      "line": 220,
      "tactics": ["noncomm_ring", "abel", "simp", "rw"],
      "depends_on": ["X_mul_X", "Y_mul_Y", "Z_mul_Z", "XY_add_YX"],
      "used_by": ["chiral_tl_recoupling_synthesis"]
    }
  ],
  "imports": [
    {"_from": "ChiralTensorRecoupling", "_to": "ChiralCausalCone"},
    {"_from": "ChiralTensorRecoupling", "_to": "Mathlib"}
  ],
  "tactics": [
    {"_from": "ChiralTensorRecoupling.e_sq", "tactic": "noncomm_ring", "count": 1},
    {"_from": "ChiralTensorRecoupling.e_sq", "tactic": "abel", "count": 2}
  ]
}
```

## Step 3: ArangoDB graph setup

```aql
// Collections
modules        // document: module metadata
theorems       // document: theorem metadata
tactics        // document: tactic reference (normalized names)
sockets        // document: unproved claims

// Edges
imports        // module → module
proves         // theorem → module (inverse: module HAS theorem)
depends_on     // theorem → theorem (dependency)
uses_tactic    // theorem → tactic
```

## Step 4: Key AQL queries

### Find all proofs using a specific tactic
```aql
FOR t IN theorems
  FILTER "noncomm_ring" IN t.tactics
  RETURN { name: t._key, module: t.module, line: t.line }
```

### Full dependency graph of e_sq
```aql
FOR v, e IN 1..10 OUTBOUND "theorems/ChiralTensorRecoupling.e_sq" depends_on
  RETURN { name: v._key, depth: LENGTH(e.paths[0].edges) }
```

### Find all sockets (unproved theorems)
```aql
FOR t IN theorems
  FILTER t.status == "socket"
  RETURN { name: t._key, module: t.module, line: t.line }
```

### Anti-pattern detection: `ring` on matrix types
```aql
FOR t IN theorems
  FILTER "ring" IN t.tactics
  FOR m IN modules
    FILTER m._key == t.module
    FILTER "Matrix" IN m.imports OR "TensorProduct" IN m.imports
    RETURN { name: t._key, module: t.module, warning: "ring on non-commutative type" }
```

## Step 5: Run

```bash
python3 scripts/parse_and_ingest.py proofs/
python3 scripts/query.py "tactics using 'ring' on matrices"
```
