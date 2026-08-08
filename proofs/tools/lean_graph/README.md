# GEPA Phase 3 — Lean Proof Graph → ArangoDB

Three-layer extraction of the Lean 4 proof universe into a queryable graph database.

```
Layer 1 (Syntax)      DumpLeanGraph.lean          Lean.Parser → JSONL
Layer 2 (Environment) tools/ExtractGraph.lean      Environment.constants → JSON
Layer 3 (InfoTree)    future                       elaboration tactic/goal metadata

                 ↓ join_syntax_env.py ↓
Layer 1+2 (Bridge)   matched records with full AST trees
                 ↓ import_arango.py ↓
ArangoDB             LeanUniverseGraph (lean_decls, syntax_nodes, references, ast_child, has_syntax)
```

**Design rule**: Lean-native extraction is authoritative. Tree-sitter / text grep are advisory, never proof sources.

## Role in the two-brain ArangoDB architecture

This directory implements brain **2**, the compiled Lean/theory AST brain.  It
must remain distinct from the agent/chat cognition brain.

| Brain | Primary database role | Vertices | Edges | Authority |
|---|---|---|---|---|
| Agent/chat cognition brain | JSON chat histories, agent steps, provenance | `steps`, spawned tasks, content-hash states | `next_step`, `spawns`, claim/support bridges | Historical/cognitive evidence |
| Compiled Lean/theory AST brain | Elaborated Lean declarations and parser AST | `lean_decls`, `syntax_nodes`, `lean_modules` | `references`, `ast_child`, `has_syntax`, `decl_root`, `lean_imports` | Formal/theorem evidence |

The compiled Lean graph answers questions that the chat graph cannot answer:

- did a declaration actually elaborate under `lake`?
- which compiled declarations does it depend on?
- which parser AST subtree produced the declaration?
- which theorem claims are backed by compiled Lean objects rather than by chat text?
- where does a proof branch terminate in a real zero/boundary/vacuum state?

The only allowed bridge from chat to theorem brain is an explicit provenance edge:

```text
chat step / paper claim
  --claims_or_cites-->
Lean declaration (`lean_decls`)
  --has_syntax / decl_root-->
AST root (`syntax_nodes`)
  --references-->
compiled proof dependencies
```

Do **not** collapse these graphs into one collection.  The chat brain is a
history/provenance DAG; this graph is the compiled mathematical DAG.

## Boundary/vacuum semantics

For graph audits, the cohomological law is:

```text
∂² = 0
```

The boundary of a boundary is the zero state.  In the graph this means terminal
or null-sector vertices are not automatically failures: they may be healthy
cohomological boundaries.  The canonical vacuum/zero hash used elsewhere in the
workspace is the SHA-256 hash of the empty string:

```text
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
```

Use this interpretation carefully:

- `content_hash == e3b0c44...` means a zero/vacuum boundary candidate.
- A compiled declaration with real `references` is theorem evidence.
- A chat node with only a zero/vacuum hash is not theorem evidence by itself.
- Regex-detected `True := trivial`, `def X := 0`, or similar vacuity patterns are
  audit signals only; confirm against the compiled Lean graph before claiming a
  proof gap or proof success.

## Hash labels

The compiled brain uses several non-interchangeable hash/key notions:

- `decl_key(name)`: deterministic Arango key for a Lean declaration name.
- `stable_key(...)`: deterministic graph key with a SHA1 prefix/suffix for AST
  nodes and edges.
- syntax/content hash: hash of source or serialized AST content.
- de-Bruijn/alpha-normal hash: intended future hash of binder-normalized terms;
  use this for proof-shape comparison only after a Lean-native normalizer emits
  it.
- vacuum hash: SHA-256 empty-string hash, the cohomological zero state.

Never identify two declarations solely because their raw text hashes match.
The authoritative identity is the elaborated declaration plus its dependency
edges in `lean_decls`/`references`.

## Quick Start

All commands run from `/home/goutev/auto/proofs/` unless stated otherwise.

```bash
# 0. Load local Arango runtime used by this workspace.
source /home/goutev/.config/arango/env.sh

# 1. Syntax dump — all files
lake env lean --run tools/lean_graph/DumpLeanGraph.lean *.lean > /tmp/syntax.jsonl

# 2. Environment dump — all declarations + dependencies
lake env lean tools/ExtractGraph.lean   # → proof_graph.json

# 2b. Optional audit/GEPA canonicalization — does not rewrite the kernel graph
python3 tools/lean_graph/canonicalize_proof_graph.py proof_graph.json

# 3. Bridge — join syntax positions with env deps, embed full AST
python3 tools/lean_graph/join_syntax_env.py \
  --syntax-jsonl /tmp/syntax.jsonl \
  --env-json proof_graph.json \
  --include-syntax-tree \
  > /tmp/bridge.jsonl

# 4. Dry-run validation (no ArangoDB needed)
python3 tools/lean_graph/import_arango.py /tmp/bridge.jsonl

# 5. ArangoDB import (requires running ArangoDB and python-arango)
python3 tools/lean_graph/import_arango.py /tmp/bridge.jsonl --execute

# 5b. Syntax-only ArangoDB import without python-arango
python3 tools/lean_graph/ingest_syntax_to_arango.py /tmp/syntax.jsonl --execute-http
```

## Mandatory read-before-write workflow for agents

Before editing Lean/SymPy code in `/home/goutev/auto`, query the existing graph
and then read the matching source ranges.  Do not guess by filenames.

```bash
cd /home/goutev/auto/proofs
source /home/goutev/.config/arango/env.sh

# Verify the graph is reachable and non-empty.
bash tools/lean_graph/aql_smoke_test.sh

# Search declaration names in the syntax graph.
python3 tools/lean_graph/aql_query.py <<'AQL'
FOR d IN syntax_decls
  FILTER CONTAINS(d.name, 'SupergradedCuntzBdG')
     OR CONTAINS(d.name, 'Poincare')
     OR CONTAINS(d.name, 'Lorentz')
  SORT d.name
  LIMIT 50
  RETURN {name: d.name, keyword: d.keyword, range: d.range}
AQL

# Search inside AST identifiers/doc atoms for concepts.
python3 tools/lean_graph/aql_query.py <<'AQL'
LET terms = ['affineSuperBracket', 'supercharge', 'pauliMomentum', 'boostX']
FOR n IN syntax_nodes
  LET txt = HAS(n,'raw') ? n.raw : (HAS(n,'value') ? n.value : '')
  FILTER txt != ''
  LET hits = (FOR t IN terms FILTER CONTAINS(txt, t) RETURN t)
  FILTER LENGTH(hits) > 0
  COLLECT decl = n.declName INTO group = {txt, range:n.range, hits:hits}
  SORT decl
  LIMIT 80
  RETURN {decl, hits: UNIQUE(FLATTEN(group[*].hits)), samples: SLICE(group,0,3)}
AQL
```

Then use `read` on the files/ranges returned by AQL.  Only after that should you
patch an existing file or add a new one.

`tools/lean_graph/aql_query.py` uses Arango's HTTP API directly and needs only
Python's standard library.  It exists because some agent environments do not
have `python-arango` installed.  For the same reason,
`tools/lean_graph/ingest_syntax_to_arango.py --execute-http` can ingest the
syntax-only graph without `python-arango`.

## Smoke Tests

```bash
bash tools/lean_graph/smoke_test.sh          # syntax JSONL shape validation
bash tools/lean_graph/bridge_smoke_test.sh   # end-to-end syntax→env bridge
```

Expected output: `bridge smoke passed` with 130+ matched declarations.

## Graph Schema (`LeanUniverseGraph`)

### Vertex Collections

| Collection | Key | Fields | Description |
|---|---|---|---|
| `lean_decls` | `decl_key(name)` | `name`, `kind`, `module`, `type`, `hasValue`, `isUnsafe`, `isAxiom` | Elaborated Lean declarations |
| `syntax_nodes` | `stable_key("syn", decl, path...)` | `kind` (`node`/`atom`/`ident`), `syntaxKind`, `range`, `value`/`raw`, `decl` | Parser AST nodes |

### Edge Collections

| Collection | From → To | Meaning |
|---|---|---|
| `references` | `lean_decls` → `lean_decls` | Environment dependency (declaration calls declaration) |
| `ast_child` | `syntax_nodes` → `syntax_nodes` | Parser parent → child in syntax tree |
| `has_syntax` | `lean_decls` → `syntax_nodes` | Declaration → its top-level syntax root |

### Key Design

- `decl_key(name)`: ASCII-safe, strips Unicode, max 200 chars. Example: `ChiralCausalCone_Plus` ← `ChiralCausalCone.σPlus`.
- `stable_key(*parts)`: SHA1-16 hex digest with human-readable prefix. Deterministic across runs.
- All edge inserts use `try/except` for idempotent re-ingestion.

## Layer 1: Syntax JSONL

Each `DumpLeanGraph.lean` record is one top-level declaration:

```json
{
  "layer": "syntax",
  "name": "ChiralTLDescent.chiral_left_tau_ideal",
  "keyword": "theorem",
  "syntax": {
    "kind": "node",
    "syntaxKind": "Lean.Parser.Command.declaration",
    "range": {"startLine": 89, "startCol": 0, "endLine": 99, "endCol": 31},
    "children": [...]
  }
}
```

Recursive syntax nodes are exactly one of:

- **`node`**: `syntaxKind` (Lean parser kind), optional `range`, `children` (array)
- **`atom`**: `syntaxKind`, optional `range`, `value` (string)
- **`ident`**: `syntaxKind`, optional `range`, `raw` (string name)

Validate shape:

```bash
lake env lean --run tools/lean_graph/DumpLeanGraph.lean TLChain.lean \
  | python3 tools/lean_graph/check_dump_shape.py --expect-keyword theorem
```

## Layer 2: Environment JSON

`tools/ExtractGraph.lean` imports all target modules and queries `Environment.constants`:

```json
{
  "name": "ChiralTLDescent.chiral_left_tau_ideal",
  "kind": "theorem",
  "type": "IsLeftTauIdeal (K := ℂ) (H := M2C) ...",
  "deps": ["ChiralTLDescent.tauL_qCrossMap_on_e", "BraidIdealDescent.tauL", ...]
}
```

The prefix filter in `ourPrefixes` controls which modules are included. Add new modules there when extending the proof base.

## AQL Query Examples

Run in ArangoDB web UI (http://localhost:8529) or via python-arango.

### Most-referenced lemmas

```aql
FOR edge IN references
  COLLECT target = edge._to WITH COUNT INTO c
  SORT c DESC LIMIT 20
  LET doc = DOCUMENT(target)
  RETURN {name: doc.name, referenced_by: c}
```

### Dependency trace (BFS from a theorem)

```aql
FOR v, e IN 1..5 OUTBOUND "lean_decls/ChiralTLDescent_chiral_left_tau_ideal" references
  RETURN {name: v.name, depth: LENGTH(e)}
```

### Find all declarations in a module

```aql
FOR decl IN lean_decls
  FILTER decl.module == "ChiralTLDescent"
  RETURN {name: decl.name, kind: decl.kind}
```

### AST size per declaration (proxy for proof complexity)

```aql
FOR decl IN lean_decls
  LET root = FIRST(FOR e IN has_syntax FILTER e._from == decl._id RETURN e._to)
  LET nodeCount = LENGTH(FOR v IN 1..50 OUTBOUND root ast_child RETURN 1)
  SORT nodeCount DESC LIMIT 10
  RETURN {name: decl.name, ast_nodes: nodeCount}
```

### Sockets: declarations with no incoming references

```aql
FOR decl IN lean_decls
  FILTER decl.kind == "def" OR decl.kind == "structure"
  LET refs = LENGTH(FOR e IN references FILTER e._to == decl._id RETURN 1)
  FILTER refs == 0
  RETURN decl.name
```

### Cross-module dependency bridges

```aql
FOR a IN lean_decls
  FILTER a.module == "ChiralTensorRecoupling"
  FOR b IN lean_decls
    FILTER b.module == "BraidIdealDescent"
    FOR v, e IN 1..5 OUTBOUND a._id references
      FILTER v._id == b._id
      RETURN {from: a.name, to: b.name, path_length: LENGTH(e)}
```

## Verified Import Results (2026-06-16)

```
bridge_records:  150
lean_decls:      181  (138 matched + 43 dependency stubs)
syntax_nodes:   5,171
references:      564
ast_child:     5,033
has_syntax:      138
```

Top-5 most-referenced: `M2C` (81), `σPlus` (40), `σMinus` (40), `σ3c` (36), `SpinPair` (23).

## Verified Import Results (2026-06-16)

```
bridge_records:  4,958
lean_decls:      1,091
syntax_nodes:   35,161
references:      3,272
ast_child:      34,395
has_syntax:        766
matched:           766
sockets:            25
sorry/admit:         0
```

Release tags: `v1.2.0`, `v1.3.0`, `v1.4.0`, `v1.5.0`.

## Lean Tensor Product Patterns (from this session)

Working with `TensorProduct` in Lean 4 is flaky. Key findings:

### Unfold BEFORE dsimp
For `tauL`/`tauR`/`qCrossMap` computations, unfold ALL maps before `dsimp`:
```lean
unfold tauL qCrossMap; dsimp; simp [TensorProduct.smul_tmul, TensorProduct.assoc_tmul]
```

### Coercion trap
`rw` can't match `(s : Submodule.Subtype)` with `s.val`. Use:
```lean
rw [show (s : SpinPair) = s.val from rfl, ← hc]
```

### Module TensorProduct.map > Algebra.TensorProduct.map
Use `TensorProduct.map` with `.toLinearMap` for clean `simp`:
```lean
def colorSwap := TensorProduct.map LinearMap.id (TensorProduct.comm ...).toLinearMap
```

### Avoid nested TensorProduct.induction_on
`M2C ⊗ (M2C ⊗ M2C)` causes `whnf` heartbeat timeout. Use `simp` on pure tensors.

### Finite spectra: fin_cases + norm_num
For 2×2 matrices or 8 Boolean states, explicit case enumeration is reliable:
```lean
ext i j; fin_cases i <;> fin_cases j <;> norm_num          -- 2×2 (4 cases)
rcases h0:w 0 <;> rcases h1:w 1 <;> rcases h2:w 2 <;> ... -- 2³ (8 cases)
```

## Files

| File | Role |
|---|---|
| `DumpLeanGraph.lean` | Layer 1: Lean `Parser` → JSONL syntax dump |
| `ExtractGraph.lean` | Layer 2: `Environment.constants` → JSON env dump |
| `join_syntax_env.py` | Bridge: join syntax + env by fully qualified name |
| `import_arango.py` | GEPA Phase 3: import bridge JSONL into ArangoDB |
| `check_dump_shape.py` | JSONL shape validator (node/atom/ident, range, children) |
| `aql_query.py` | Dependency-light AQL runner using ArangoDB HTTP API and `/home/goutev/.config/arango/env.sh` |
| `aql_smoke_test.sh` | Verifies local Arango AST graph counts and basic declaration search |
| `canonicalize_proof_graph.py` | Derived audit graph: stable order, de-duplicated deps, autogenerated/vacuity hints |
| `normalize_syntax_index.py` | Compact declaration index from full syntax records |
| `ingest_syntax_to_arango.py` | Syntax-only ArangoDB ingestion (`LeanSyntaxGraph`) |
| `ingest_bridge_to_arango.py` | Bridge edge ingestion (`syntax_elaborates_to`) |
| `smoke_test.sh` | Syntax dump + shape validation |
| `bridge_smoke_test.sh` | End-to-end syntax→env→bridge→dry-run |
