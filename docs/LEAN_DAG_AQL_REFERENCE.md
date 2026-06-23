# Lean DAG AQL Reference — Schema, Queries, and Theory Closure

## Architecture Overview

Three layers, from raw Lean to queryable graph:

```
Layer 1 (Syntax)    DumpLeanGraph.lean           Lean.Parser → JSONL AST trees
Layer 2 (Env)       ExtractGraph.lean / leantrail  Environment.constants → deps
Layer 3 (Bridge)    join_syntax_env.py             matched records, full AST context

                    ↓ import_arango.py / arango_ingest.py ↓

ArangoDB            ig_nodes / ig_edges   (leantrail)
                    lean_decls / syntax_nodes / references / ast_child / has_syntax (GEPA)
```

## The Schema (Two Collections, Three Edge Kinds)

This is deliberately minimal — the simplicity is what makes AQL fast.

### Nodes (`ig_nodes` / `lean_decls`)

| Field | Type | Description |
|:---|:---|:---|
| `_key` | string | Stable node ID: `ModulePath::declName` |
| `name` | string | Short declaration name |
| `kind` | string | `Theorem` `Lemma` `Definition` `Axiom` `Structure` `Inductive` `Instance` |
| `module` | string | Namespace prefix (e.g. `DAG.LaplacianRank`) |
| `file` | string | Relative source path |
| `line` | int | Declaration line number |
| `role` | string | `owner` `translator` `pure_conductor` `closure_debt` `dead_socket` `contaminated` `fake_transport` |
| `rep_depth` | string | `L0_Count` → `L5_ThermodynamicClosure` (representation layer) |
| `module_family` | string | Carrier algebraic family tag |
| `attrs` | object | `structural_dedup`, `commit_sha`, `toolchain`, `artifact_version` |

### Edges (`ig_edges` / `references`)

| Field | Type | Description |
|:---|:---|:---|
| `_from` | string | Source node `_key` |
| `_to` | string | Target node `_key` |
| `kind` | string | `depends_type` `depends_value` `contains` |
| `weight` | float | Dependency strength 0..1 |
| `evidence_ref` | string | `file:line` or sha256 of proof excerpt |

### Edge Kinds

| Kind | Direction | Meaning |
|:---|:---|:---|
| `depends_type` | OUTBOUND | B appears in A's type signature — B must compile first |
| `depends_value` | OUTBOUND | B is used in A's proof body — B's truth is a premise for A |
| `contains` | OUTBOUND | Module M contains declaration D — hierarchical grouping |

### Node Roles (Closure Status)

| Role | Meaning | Impact |
|:---|:---|:---|
| `pure_conductor` | 0 sorries, fully proved, no upstream debt | clean |
| `owner` | locally proved, all upstream deps are clean | clean |
| `translator` | bridges two module families | clean |
| `closure_debt` | has explicit `_sorry` structural field | honest debt |
| `contaminated` | transitively depends on a `closure_debt` node | inherited debt |
| `dead_socket` | unused, no incoming edges | orphaned |
| `fake_transport` | `True := sorry` placeholder | toxic — blocks real closure |

---

## AQL Query Arsenal

Run in ArangoDB web UI (http://localhost:8529) or via `arango_dump.py`.

### 1. Causal Cone (Downstream) — What does this node depend on?

```aql
FOR v, e, p IN 1..@max_depth OUTBOUND @seed_id @@edges
  OPTIONS {uniqueVertices: "global", bfs: true}
  FILTER e.kind IN ["depends_type", "depends_value"]
  RETURN {
    node: {id: v._id, name: v.name, kind: v.kind, module: v.module, role: v.role},
    depth: LENGTH(p.edges),
    path: p.vertices[*]._id
  }
```

### 2. Causal Cone (Upstream) — What depends on this node?

```aql
FOR v, e, p IN 1..@max_depth INBOUND @seed_id @@edges
  OPTIONS {uniqueVertices: "global", bfs: true}
  FILTER e.kind IN ["depends_type", "depends_value"]
  RETURN {
    node: {id: v._id, name: v.name, kind: v.kind, module: v.module, role: v.role},
    depth: LENGTH(p.edges),
    path: p.vertices[*]._id
  }
```

### 3. Multi-Apex Cone — Shared dependency subgraph of several theorems

```aql
FOR seed IN @seed_ids
  FOR v, e, p IN 1..@max_depth ANY seed @@edges
    OPTIONS {uniqueVertices: "global", bfs: true}
    FILTER e.kind IN ["depends_type", "depends_value"]
    RETURN DISTINCT {
      node: {id: v._id, name: v.name, module: v.module, role: v.role},
      seed: seed,
      depth: LENGTH(p.edges)
    }
```

### 4. Shortest Path Between Two Theorems

```aql
FOR v, e IN ANY SHORTEST_PATH @src TO @dst @@edges
  FILTER e.kind IN ["depends_type", "depends_value"]
  RETURN {
    vertex: {id: v._id, name: v.name, kind: v.kind, module: v.module},
    edge: {kind: e.kind, evidence: e.evidence_ref}
  }
```

### 5. Frontier — All Sorried/Contaminated Nodes

```aql
FOR n IN @@nodes
  FILTER n.role IN ["contaminated", "closure_debt", "dead_socket"]
  SORT n.module, n.name
  RETURN {id: n._id, name: n.name, kind: n.kind, module: n.module, role: n.role}
```

### 6. Blast Radius — For each sorried node, how many clean nodes would be rescued?

```aql
FOR n IN @@nodes
  FILTER n.role IN ["contaminated", "closure_debt"]
  LET upstream = LENGTH(
    FOR v IN 1..99 INBOUND n._id @@edges
      FILTER v.role NOT IN ["contaminated", "closure_debt"]
      RETURN v
  )
  SORT upstream DESC
  RETURN {id: n._id, name: n.name, module: n.module, role: n.role, blast_radius: upstream}
```

### 7. Missing Bridges — Theorems in different SCCs with shared name tokens

These are candidates where adding a proof connecting two disconnected components would close multiple gaps at once.

```aql
FOR a IN @@nodes
  FILTER a.kind IN ["Theorem", "Lemma"] AND a.role == "pure_conductor"
  FOR b IN @@nodes
    FILTER b.kind IN ["Theorem", "Lemma"] AND b.role == "closure_debt"
    FILTER a._key < b._key
    FILTER a.module != b.module
    LET shared = LENGTH(
      FOR tok IN TOKENS(a.name, "[_]+")
        FILTER tok IN TOKENS(b.name, "[_]+")
        RETURN tok
    )
    FILTER shared >= 2
    RETURN {conductor: a.name, target: b.name, shared_tokens: shared}
```

### 8. Cross-Layer Edge Audit — Detect regressive dependencies

```aql
FOR e IN @@edges
  FILTER e.kind IN ["depends_type", "depends_value"]
  LET src = DOCUMENT(e._from)
  LET dst = DOCUMENT(e._to)
  FILTER src != null AND dst != null AND src.rep_depth != dst.rep_depth
  COLLECT from_depth = src.rep_depth, to_depth = dst.rep_depth WITH COUNT INTO cnt
  SORT cnt DESC
  RETURN {from: from_depth, to: to_depth, count: cnt}
```

### 9. GEPA Universe: `sorry` Scan Through Full AST

Requires the three-layer GEPA pipeline (`lean_decls` + `syntax_nodes` + `has_syntax` + `ast_child`):

```aql
FOR decl IN lean_decls
  FOR ast_root IN 1..1 OUTBOUND decl has_syntax
    FOR ast_node IN 1..25 OUTBOUND ast_root ast_child
      FILTER ast_node.atom == "sorry" OR ast_node.ident == "sorry"
      RETURN {declaration: decl.name, range: ast_node.range}
```

### 10. GEPA Universe: Tactic Audit Under a Target Declaration

```aql
FOR thm IN lean_decls
  FILTER thm.name == "DAG.LaplacianRank.laplacian_rank_eq_add_rank"
  FOR ast_root IN 1..1 OUTBOUND thm has_syntax
    FOR ast_node IN 1..15 OUTBOUND ast_root ast_child
      FILTER ast_node.syntaxKind LIKE "%Tactic%"
      RETURN {syntaxKind: ast_node.syntaxKind, tactic: ast_node.ident, range: ast_node.range}
```

### 11. Top 20 Most-Depended-On Lemmas

```aql
FOR e IN @@edges
  FILTER e.kind IN ["depends_type", "depends_value"]
  COLLECT target = e._to WITH COUNT INTO freq
  SORT freq DESC
  LIMIT 20
  LET node = DOCUMENT(target)
  RETURN {name: node.name, module: node.module, used_by: freq}
```

### 12. Dependency Depth Distribution

```aql
FOR n IN @@nodes
  FILTER n.kind IN ["Theorem", "Lemma"]
  LET depth = LENGTH(FOR v IN 1..20 OUTBOUND n._id @@edges RETURN v)
  COLLECT d = depth WITH COUNT INTO cnt
  SORT d ASC
  RETURN {depth: d, count: cnt}
```

### 13. Isolation Check — Nodes With Zero Dependencies

```aql
FOR n IN @@nodes
  FILTER n.kind IN ["Theorem", "Lemma", "Definition"]
  LET incoming = LENGTH(FOR e IN @@edges FILTER e._to == n._id RETURN 1)
  LET outgoing = LENGTH(FOR e IN @@edges FILTER e._from == n._id RETURN 1)
  FILTER incoming == 0 AND outgoing == 0
  RETURN {name: n.name, kind: n.kind, module: n.module}
```

### 14. Theory Closure Score

```aql
LET total = LENGTH(FOR n IN @@nodes FILTER n.kind != "Axiom" RETURN n)
LET clean = LENGTH(
  FOR n IN @@nodes
    FILTER n.role IN ["pure_conductor", "owner", "translator"]
    RETURN n
)
RETURN {
  total: total,
  clean: clean,
  debt: total - clean,
  pct_clean: clean * 100 / total
}
```

### 15. Enumerate All SCCs

```aql
FOR n IN @@nodes
  FILTER n.kind IN ["Theorem", "Lemma"]
  COLLECT scc = n.attrs.scc_id INTO group
  LET members = LENGTH(group)
  SORT members DESC
  LIMIT 20
  RETURN {scc: scc, members: members}
```

---

## Theory Closure via AQL — The Workflow

### Step 1: Extract the AST graph

```bash
python3 tools/leantrail/ast_extract.py        \
  --root lean/                                 \
  --out artifacts/leantrail/lean_ast_graph.json \
  --jsonl  # produces nodes.jsonl + edges.jsonl for ArangoDB
```

### Step 2: Ingest into ArangoDB

```bash
python3 tools/leantrail/arango_ingest.py       \
  --input-dir artifacts/leantrail/             \
  --nodes-collection ig_nodes                  \
  --edges-collection ig_edges
```

### Step 3: Compute roles (contamination propagation)

```bash
python3 tools/leantrail/shadow_ledger.py       \
  --in artifacts/leantrail/lean_ast_graph.json \
  --out artifacts/leantrail/ledger.json
```

### Step 4: Run AQL queries to find closure targets

```bash
# Find the frontier
python3 tools/leantrail/arango_dump.py         \
  --query frontier --out frontier.json

# Find highest-impact closure targets
python3 tools/leantrail/arango_dump.py         \
  --query blast-radius --out blast.json

# Find missing bridges between components
python3 tools/leantrail/aql_schema.py          \
  --graph artifacts/leantrail/lean_ast_graph.json \
  --missing-bridges --out bridges.json
```

### Step 5: Close the highest-impact gap

For each target in `blast.json` (sorted by `blast_radius` descending):

1. Pull the causal cone to see dependencies:
   ```bash
   python3 tools/leantrail/arango_dump.py --cone-downstream <target_id>
   ```

2. Search for existing proofs:
   ```bash
   python3 tools/leantrail/oracle_search.py --search "<target_name> proof mathlib lemma"
   ```

3. Generate candidate lemmas:
   ```bash
   python3 tools/leantrail/oracle_search.py --ask "Prove <statement>" --compile
   ```

4. Apply the fix and re-extract:
   ```bash
   python3 tools/leantrail/ast_extract.py ...
   ```

5. Verify closure score improved:
   ```bash
   python3 tools/leantrail/aql_schema.py --closure
   ```

---

## Python-Native Topology (No ArangoDB Required)

The `aql_schema.py` `TopologyAnalyzer` class provides the same queries on the JSON graph export without ArangoDB:

```python
from tools.leantrail.aql_schema import TopologyAnalyzer
import json

graph = json.loads(Path("artifacts/leantrail/lean_ast_graph.json").read_text())
ta = TopologyAnalyzer().load(graph)

# Causal cone
cone = ta.causal_cone("DAG.LaplacianRank::laplacian_rank_eq_add_rank", max_depth=3)

# Frontier nodes
frontier = ta.frontier_nodes()

# Blast radius
blast = ta.blast_radius(min_upstream=1)

# Missing bridges
bridges = ta.detect_missing_bridges()

# Closure score
score = ta.closure_score()
print(f"Theory: {score['pct_clean']}% clean ({score['clean']}/{score['total']})")
```

Performance: BFS on ~10k nodes / ~50k edges completes in <100ms on a laptop. The deliberately minimal schema (two collections, three edge kinds) keeps the graph sparse enough for O(V+E) traversal.

---

## ArangoDB Connection

Configure in the shell environment or `~/.config/arango/env.sh`:

```bash
export ARANGO_ENDPOINT="http://localhost:8529"
export ARANGO_DATABASE="LeanAST"
export ARANGO_USERNAME="root"
export ARANGO_ROOT_PASSWORD=""
```

If `python-arango` is unavailable, `arango_dump.py` falls back to raw HTTP `_api/cursor` POST with Basic auth — no pip dependency required.
