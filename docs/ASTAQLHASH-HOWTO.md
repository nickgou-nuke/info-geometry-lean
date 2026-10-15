# Complete ArangoDB + AST/AQL Hash-Based Search Methodology

## Live-code audit status (2026-10-03)

This HOWTO is grounded against the live repository implementation, not against
prose memory of the toolchain.  The authoritative implementation surfaces are:

- `lean/DAG/Indexer.lean`: emits `DeclNode` / `StreamDecl` records with
  `typeFingerprint`, `valueFingerprint`, and `shapeHash`, plus stream edges
  with `src`, `dst`, and `kind`.
- `lean/DAG/ExprFingerprint.lean`: defines `ExprFingerprint` and
  `computeFingerprint`; `shapeHash` is a `UInt64` field inside this structure.
- `lean/DAG/SearchByHash.lean`: native Lean-side hash search over imported
  modules.
- `tools/infra/refresh_decl_graph.py`: supports `--stream`, `--arango-db`,
  `--run-mode`, `--import-root`, and `--namespace`.
- `tools/infra/arango_env.py` / `src/igf/config/env_aliases.py`: repo-owned
  Arango credential/config loading.  Default endpoint is
  `http://127.0.0.1:8530`; default database is `infogeometry`; default env file
  is `configs/local/hive_arango.env`.
- `tools/infra/hash_owner_map.py`: offline/native shape-hash owner lookup via
  Lean import plus source owner scan.

Important boundary:

- Shape/value hashes are structural navigation evidence, not mathematical proof.
- A shape cluster may identify duplicated proof shape, vacuous sockets, or a
  useful owner corridor; it does not by itself prove a theorem.
- Before using any older bridge/helper script, inspect its current source for
  credential handling, database/collection defaults, and write behavior. Do
  not treat a generated bridge result as proof. Prefer the repository env
  loader and the read-only-by-default query interface below; record the exact
  tool and source revision used.

### Typed semantic-edge metadata

Declaration owners may optionally carry `@[edge_kind <identifier>]`. Supported
identifiers are `equivalence`, `representation`, `analogy`,
`conjectural_bridge`, and `proof`; `proof` is exported as the canonical
semantic kind `theorem`, since `theorem` is a Lean command keyword and cannot
be parsed as an attribute identifier. This metadata classifies the declaration
that owns a bridge. It does not change compiler dependency kinds (`type` and
`value`) and never promotes a conjectural bridge to a proof.

The streaming declaration records preserve `edge_kind:<kind>` in `attrs`.
`materialize_lossless_infotree.py` projects it onto raw nodes as
`edge_kind`/`edge_kinds` and onto dependency edges as
`semantic_kind`/`semantic_kinds`, while retaining AST/value/shape hashes.
Thus AQL/hash queries can filter semantic role and still resolve the owner by
`valueFingerprint.shapeHash`; Lean source and kernel checking remain authority.

## Authoritative causal-cone graph path

The compiler-backed declaration graph is the primary graph authority for causal-cone prompt construction:

- `decls`: Lean declaration vertices emitted by the current declaration stream;
- `edges`: typed declaration dependency edges emitted by the same stream;
- `valueFingerprint.shapeHash`: AST/value structural hash carried by each declaration vertex.

`tools/infra/arango_causal_chiral_cone_prompt.py` resolves declarations from
`decls` first and traverses `edges` directly. It uses `raw_info_nodes` and SCC
overlays as enrichment when matching RawInfoTree coverage exists. This keeps
compiler-backed declarations queryable even when raw infotree coverage is
incomplete.

Authoritative-first probe:

```bash
python3 tools/infra/arango_causal_chiral_cone_prompt.py \\
  --decl InfoGeometry.Algebra.G2.g2_twist_closure \\
  --decls-collection decls \\
  --edges-collection edges \\
  --json-out /tmp/g2_twist_closure.packet.json
```

The packet records `apex.authority = "decls"` and preserves the declaration
fingerprint fields in the apex node for subsequent ASTAQL grouping. The packet
is navigation context; Lean source and kernel checks remain proof authority.

For crossing concepts, use the multi-apex/multi-cone mode:

```bash
python3 tools/infra/arango_causal_chiral_cone_prompt.py \\
  --decl-multi \\
  'InfoGeometry.Algebra.G2.g2_twist_closure,InfoGeometry.Algebra.Cuntz.CuntzNAlgebra.isometry' \\
  --backward-depth 4 \\
  --forward-depth 4 \\
  --json-out /tmp/cross-concepts.packet.json
```

This traverses `ANY` over the authoritative `edges` graph, preserves seed
provenance for every cone row, and reports nodes reached from multiple apices
as `shared_nodes`. It is the cross-concept bridge for identifying shared Lean
prerequisites and missing connecting declarations.

## Strict execution order: source search, read-only query, optional refresh

For ASTAQLHASH clone or sorry-equivalence work, freshness matters, but a graph
refresh is destructive and is not a prerequisite for beginning investigation.
Run the stages in this order and stop when a prerequisite fails:

1. Establish the source scope and search all relevant source roots recursively.
   The graph never substitutes for this step.
2. Inspect local/live graph metadata and query existing data read-only through
   `arango_causal_memory.py query`. Label freshness unknown unless metadata
   connects the graph generation to the current source/olean state.
3. Use fingerprints, attrs, edges, and causal-cone packets to prioritize owner
   inspection; do not call a hash cluster an equivalence class or sorry proof.
4. Open owner files and inspect imports/dependents. Use the Lean kernel or
   locked build to validate claims.
5. Refresh only if stale/missing graph data materially blocks the work, and
   only under the explicit live-replacement authorization and recovery process
   in “Phase 2” below.

### Refresh is destructive

The legacy `refresh_decl_graph.py --stream` mode (without `--generation-id`)
**truncates the live collections before it writes any data.** In
`tools/infra/refresh_decl_graph.py` that compatibility path does

```python
if not db.has_collection(coll_name):
    db.create_collection(coll_name, edge=is_edge)
else:
    db.collection(coll_name).truncate()
```

and the batch importer documents itself as *"Append one stream batch to a collection
truncated before this run."*

Consequences for the legacy mode:

- The live `decls` and `edges` collections are **emptied at the start of the run**.
  A non-empty graph does not survive a failed or interrupted refresh.
- If the stream fails after the truncate, the graph is left empty or partial. There
  is no rollback in this tool.
- Any index built by a narrower import root, a different namespace, or a bounded run
  will *replace* the full graph rather than add to it.
- Therefore: treat refresh as **maintenance with explicit pre-authorization**, never
  as a routine prelude to a search. Prefer `hash_owner_map.py` and
  `arango_causal_memory.py local-search` for read-only work.

Full-graph invariant:

- The canonical refresh imports `InfoGeometry.All` and indexes the complete
  reachable `InfoGeometry` declaration namespace.
- Do not substitute a narrower import root or namespace, truncate the emitted
  declaration stream, sample files, cap the number of declarations or edges,
  or confuse bounded post-index query traversal with graph construction.
- Traversal depths such as `--backward-depth` and `--forward-depth` limit only a
  requested query packet; they never authorize shortening the stored graph.

The pinned repository workflow does not run `lake update` as part of this
sequence. Dependency and toolchain pins are compatibility state; refresh only
the declaration graph and generated graph artifacts.

Canonical streaming refresh command (destructive; execute only after the
authorization and recovery checks in Phase 2):

```bash
# Requires the existing executable and imported oleans. This command truncates
# the selected graph collections before streaming replacement data.
python3 tools/infra/refresh_decl_graph.py \\
  --stream \\
  --run-mode exe \\
  --skip-prebuild \\
  --import-root InfoGeometry.All \\
  --namespace InfoGeometry \\
  --arango-db infogeometry
```

Canonical AQL wrapper query for candidate sorry-equivalence classes:

```bash
python3 tools/infra/arango_causal_memory.py query '
FOR d IN decls
  FILTER d.valueFingerprint != null
  FILTER d.name LIKE "%sorry%"
      OR d.name LIKE "%_True%"
      OR d.name LIKE "%_certificate%"
      OR d.name LIKE "%_witness%"
  COLLECT hash = d.valueFingerprint.shapeHash INTO members
  FILTER hash != null
  RETURN {
    valueShapeHash: hash,
    declarations: members[*].d.name
  }
'
```

The returned classes are navigation evidence only. A class is not a proof of
vacuity, equivalence, or unsoundness until the cited owner declarations are
read and kernel-audited.

### Append-only generation mode

For a non-destructive declaration-DAG refresh, pass a fresh generation ID and
the caller-computed fingerprint for the exact toolchain, manifest, build
inputs, and imported environment. The script creates `decls_g_ID` and
`edges_g_ID`; it refuses to reuse existing generation collections and writes
`decl_graph_generations/ID` with `status: complete` only after ingest and edge
validation finish. Older generations remain untouched. The generation ID is
limited to 32 letters, digits, `_`, or `-`.

```bash
python3 tools/infra/refresh_decl_graph.py \\
  --stream --run-mode exe --skip-prebuild \\
  --import-root InfoGeometry.All --namespace InfoGeometry \\
  --arango-db infogeometry \\
  --generation-id <fresh-id> \\
  --build-fingerprint <toolchain-manifest-olean-source-fingerprint>
```

Query the selected generation with
`arango_causal_chiral_cone_prompt.py --generation-id ID`; it maps the default
`decls` and `edges` names to those generation collections. Existing readers
that omit this option continue to address the legacy collections.

The raw InfoTree importer has a parallel immutable mode. Supplying
`--build-fingerprint` derives a 24-hex generation ID from that fingerprint and
the actual exported JSONL/metadata bytes, writes all rows and edges into
generation-specific collections, and publishes a complete record in
`raw_infotree_generations`. Reusing an already-present generation is rejected;
`--drop-existing` is incompatible with this mode. The ordinary importer path
retains its existing replacement behavior.

```bash
python3 tools/infra/arango_raw_infotree_ingest.py \\
  --input-dir <validated-export-dir> \\
  --build-fingerprint <toolchain-manifest-olean-source-fingerprint>
```

Neither graph mode is a source of proof identity. Raw InfoTree keys and
expression fingerprints are scoped navigation data; proof replay still needs
the exact source snapshot, request/tactic sequence, and compatible Lean
environment. `pantograph_arango_stream.py --source-snapshot FILE` stores that
source text by SHA-256 and logs each raw Pantograph request/response in
append-only collections. Without `--source-snapshot`, its session record
explicitly marks the replay basis as request-log-only.

## Prerequisites

```bash
# 1. ArangoDB running on localhost:8530 (repo default)
# 2. Python arango driver: pip install python-arango
# 3. Lean 4 + Lake with dagIndexer target built
# 4. The pinned Mathlib cache is already populated before this workflow starts.
```

---

## Phase 1: Initialize ArangoDB Environment

```bash
# 1.1 Load ArangoDB credentials (one-time local setup)
# Prefer editing configs/local/hive_arango.env yourself. Do not commit it.
# Supported aliases include ARANGO_USER/ARANGO_USERNAME and
# ARANGO_PASS/ARANGO_PASSWORD.
mkdir -p configs/local
chmod 700 configs/local
$EDITOR configs/local/hive_arango.env

# 1.2 Verify connection
python3 -c "
from arango import ArangoClient
from tools.infra.arango_env import (
    load_repo_arango_env,
    arango_endpoint,
    arango_username,
    arango_password,
    arango_database,
)
from pathlib import Path
load_repo_arango_env(Path('.').resolve())
client = ArangoClient(hosts=arango_endpoint())
db = client.db(arango_database(), username=arango_username(), password=arango_password())
print('Connected:', db.name)
print('Collections:', [c['name'] for c in db.collections() if not c['name'].startswith('_')])
"
```

---

## Phase 2: Verify & Stream the Full Declaration Graph to ArangoDB

```bash
# 2.1 Confirm explicit authorization to replace decls and edges in the exact
#    target database; confirm backup/recovery and maintenance window first.
# 2.2 Inspect worktree state and active compiler/refresh processes. Do not
#    overlap builds, graph refreshes, or kill another running task.
git status --short
pgrep -a -x lake || true
pgrep -a -x lean || true
pgrep -af 'refresh_decl_graph|dagIndexer' || true

# 2.3 Confirm exact Arango endpoint/database via the repo env loader without
#    printing credential values. Confirm the existing executable and cache.
test -x .lake/build/bin/dagIndexer

# 2.4 Only after the authorization gate above, stream the complete declared
#    InfoGeometry export. The stream path replaces the live collections.
python3 tools/infra/refresh_decl_graph.py \
  --stream \
  --run-mode exe \
  --skip-prebuild \
  --import-root InfoGeometry.All \
  --namespace InfoGeometry \
  --arango-db infogeometry

# 2.4 Verify import
python3 -c "
from arango import ArangoClient
from pathlib import Path
from tools.infra.arango_env import (
    load_repo_arango_env,
    arango_endpoint,
    arango_username,
    arango_password,
    arango_database,
)
load_repo_arango_env(Path('.').resolve())
client = ArangoClient(hosts=arango_endpoint())
db = client.db(arango_database(), username=arango_username(), password=arango_password())
print('decls:', db.collection('decls').count())
print('edges:', db.collection('edges').count())
"
```

Required validation is structural, not a frozen count: both collections must be
nonempty, every retained edge must resolve both endpoints in `decls`, and the
streamer must report the complete emitted/orphaned/retained edge counts.  Counts
change with the checkout.

Historical reference only — not a current expected count: a refresh on
2026-08-08 (`InfoGeometry.All`, namespace `InfoGeometry`) reported 130772
declarations, 5077300 emitted dependency edges, 849775 retained
endpoint-valid edges, and 0 orphan edges after validation. Counts vary by
revision, filters, and exporter configuration; validate against the output of
the exact run being audited.

---

## Phase 3: Core AST/AQL Hash-Based Searches

### 3.0 Native/offline owner lookup before live Arango

Use this when you have a `shapeHash` and want a source-level owner map without
depending on a live Arango connection:

```bash
python3 tools/infra/hash_owner_map.py 3892707284033108221 40 \
  > artifacts/dag/hash_owner_3892707284033108221.json
```

This invokes Lean over `InfoGeometry.All`, recomputes value-expression
fingerprints with `DAG.computeFingerprint`, and then scans Lean source owners
for the sampled declarations.  Treat the output as navigation evidence: open
the cited owner files and verify the actual theorem bodies before editing or
claiming closure.

### 3.1 Find Candidate Groups by ShapeHash (Coarse Structure)

```python
from arango import ArangoClient
from pathlib import Path
from tools.infra.arango_env import (
    load_repo_arango_env,
    arango_endpoint,
    arango_username,
    arango_password,
    arango_database,
)

load_repo_arango_env(Path('.').resolve())
client = ArangoClient(hosts=arango_endpoint())
db = client.db(arango_database(), username=arango_username(), password=arango_password())

# Find candidate groups by coarse shape fingerprint; this does not establish
# structural identity. Inspect the JSON type emitted by this graph generation.
q = '''
FOR d IN decls
  COLLECT hash = d.shapeHash.shapeHash WITH COUNT INTO c
  FILTER c > 1
  SORT c DESC
  LIMIT 20
  RETURN {hash: hash, count: c}
'''
for row in db.aql.execute(q):
    print(f'{row["hash"]}: {row["count"]} decls')

# Query one candidate group using a bind variable; historical hash values and
# group sizes are not stable declaration identifiers.
target_hash = "<hash returned by the query>"
q2 = '''
FOR d IN decls
  FILTER d.shapeHash.shapeHash == @targetHash
  RETURN {{name: d.name, kind: d.kind, module: d.module, attrs: d.attrs}}
'''
for doc in db.aql.execute(q2, bind_vars={"targetHash": target_hash}):
    print(f'{doc["name"]} ({doc["kind"]}) - {doc["module"]} | attrs: {doc["attrs"]}')
```

### 3.2 Find Candidate Groups by ValueFingerprint (Not Proof Identity)

```python
# Find candidate value-fingerprint groups. A finite hash match is not proof
# identity, theorem equivalence, or evidence that either declaration is hollow.
q = '''
FOR d IN decls
  FILTER d.valueFingerprint != null
  COLLECT hash = d.valueFingerprint.shapeHash WITH COUNT INTO c
  FILTER c > 1
  SORT c DESC
  LIMIT 20
  RETURN {hash: hash, count: c}
'''
for row in db.aql.execute(q):
    print(f'{row["hash"]}: {row["count"]} decls')

# Query declarations in one candidate group using a bind variable.
target_value_hash = "<hash returned by the query>"
q2 = '''
FOR d IN decls
  FILTER d.valueFingerprint != null
  FILTER d.valueFingerprint.shapeHash == @targetHash
  RETURN {name: d.name, kind: d.kind, module: d.module, attrs: d.attrs}
'''
for doc in db.aql.execute(q2, bind_vars={"targetHash": target_value_hash}):
    print(f'{doc["name"]} ({doc["kind"]}) - {doc["module"]}')
```

### 3.3 Search by Attributes (Closure Debt / Sorry Markers)

```python
# Find declarations with specific attrs (closure debt markers)
q = '''
FOR d IN decls
  FILTER d.attrs != [] AND (POSITION(d.attrs, "infrastructure") != null OR POSITION(d.attrs, "sorry") != null)
  RETURN {name: d.name, kind: d.kind, module: d.module, attrs: d.attrs}
'''
for doc in db.aql.execute(q):
    print(f'{doc["name"]} ({doc["kind"]}) - {doc["module"]} | {doc["attrs"]}')

# Find declarations by rep_depth tag
q2 = '''
FOR d IN decls
  FILTER d.attrs != [] AND POSITION(d.attrs, "rep_depth:krein") != null
  RETURN {name: d.name, kind: d.kind, module: d.module, attrs: d.attrs}
'''
```

### 3.4 Search by Dependency Edges (Call Graph) — CORRECTED

```python
# Resolve exact declaration identity first; never derive a declaration key from
# its expression hash. Edge documents use Arango _from/_to fields.
target_name = "<fully qualified Lean declaration>"
target_id = next(db.aql.execute(
    'FOR d IN decls FILTER d.name == @name RETURN d._id',
    bind_vars={"name": target_name}), None)
if target_id is None:
    raise LookupError("declaration is absent from this graph generation")

# Incoming edges (confirm orientation in Indexer.lean before calling these
# callers/dependents).
q = '''
FOR e IN edges
  FILTER e._to == @targetId
  LET src = DOCUMENT(e._from)
  FILTER src != null
  RETURN {caller: src.name, kind: src.kind, module: src.module}
'''
incoming = db.aql.execute(q, bind_vars={"targetId": target_id})

# Outgoing edges in the opposite direction.
q2 = '''
FOR e IN edges
  FILTER e._from == @targetId
  LET dst = DOCUMENT(e._to)
  FILTER dst != null
  RETURN {callee: dst.name, kind: dst.kind, module: dst.module}
'''
outgoing = db.aql.execute(q2, bind_vars={"targetId": target_id})
```

### 3.5 Search by Module/Kind Filters

```python
# Find all theorems in a module
q = '''
FOR d IN decls
  FILTER d.module == "InfoGeometry.Core.GrandCanonical" AND d.kind == "theorem"
  RETURN {name: d.name, attrs: d.attrs}
'''

# Find all inductive types
q2 = '''
FOR d IN decls
  FILTER d.kind == "inductive"
  RETURN {name: d.name, module: d.module}
'''
```

### 3.6 Edge Validation — CRITICAL

```python
# Filter edges to only those where BOTH endpoints exist in decls
q = '''
FOR e IN edges
  LET from_doc = DOCUMENT(e._from)
  LET to_doc = DOCUMENT(e._to)
  FILTER from_doc != null AND to_doc != null
  RETURN e
'''
```

---

## Phase 4: AQL Graph Traversal (Advanced)

### 4.1 Find Strongly Connected Components (if hydrate ran)

```python
# Only available if hydrate step ran and created scc_nodes collection
q = '''
FOR scc IN scc_nodes
  COLLECT id = scc.scc_id WITH COUNT INTO c
  FILTER c > 1
  SORT c DESC
  LIMIT 10
  RETURN {scc_id: id, size: c}
'''
```

### 4.2 Find Bounded Paths Between Two Declarations

```python
# Requires graph definition or Pregel. Use edge traversal for simple cases.
from_decl = "InfoGeometry.Core.GrandCanonical.partitionGC"
to_decl = "InfoGeometry.Core.GrandCanonical.responseMatrix"

# Resolve document ids via bind variables and fail explicitly when either
# declaration is absent from this graph generation.
from_id = next(db.aql.execute(
    'FOR d IN decls FILTER d.name == @name RETURN d._id',
    bind_vars={"name": from_decl}), None)
to_id = next(db.aql.execute(
    'FOR d IN decls FILTER d.name == @name RETURN d._id',
    bind_vars={"name": to_decl}), None)
if from_id is None or to_id is None:
    raise LookupError("one or both declarations are absent from this graph")

# A bounded traversal is not a shortest-path query and does not imply graph
# completeness.
q2 = '''
FOR v, e IN 1..5 OUTBOUND @startId edges
  FILTER v._id == @targetId
  RETURN {vertex: v.name, edge: e.kind}
'''
paths = db.aql.execute(q2, bind_vars={"startId": from_id, "targetId": to_id})
```

### 4.3 Dominators (Only if hydrate step ran)

```python
# Only available if hydrate step created dominators collection
q3 = '''
FOR d IN dominators
  FILTER d.idom != null
  RETURN {node: d.name, idom: d.idom}
'''
```

---

## Phase 5: Complete Cache-Preserving Full-Graph Workflow Script

```bash
#!/bin/bash
# full_refresh_and_search.sh

set -euo pipefail

echo "=== Phase 1: Verify no competing compiler task ==="
if pgrep -x lake >/dev/null || pgrep -x lean >/dev/null; then
  echo "Refusing to start: a Lean/Lake process is already active" >&2
  exit 1
fi

echo "=== Phase 2: Verify existing indexer ==="
test -x .lake/build/bin/dagIndexer

echo "The stream refresh truncates decls and edges in the target database."
echo "Confirm explicit authorization, exact target, and recovery plan first."
read -r -p "Type infogeometry to authorize this target: " approved_db
if [[ "$approved_db" != "infogeometry" ]]; then
  echo "Target not confirmed; refusing refresh." >&2
  exit 2
fi

echo "=== Phase 3: Stream FULL InfoGeometry declaration graph ==="
python3 tools/infra/refresh_decl_graph.py \
  --stream \
  --run-mode exe \
  --skip-prebuild \
  --import-root InfoGeometry.All \
  --namespace InfoGeometry \
  --arango-db infogeometry

echo "=== Phase 4: Run Searches ==="
python3 <<'PYEOF'
from arango import ArangoClient
from pathlib import Path
from tools.infra.arango_env import (
    load_repo_arango_env,
    arango_endpoint,
    arango_username,
    arango_password,
    arango_database,
)

load_repo_arango_env(Path('.').resolve())
client = ArangoClient(hosts=arango_endpoint())
db = client.db(arango_database(), username=arango_username(), password=arango_password())

print("=== DECLARATION STATS ===")
print(f"Decls: {db.collection('decls').count()}")
print(f"Edges: {db.collection('edges').count()}")

print("\n=== TOP 10 COARSE SHAPE-FINGERPRINT GROUPS (CANDIDATES) ===")
for row in db.aql.execute('''
  FOR d IN decls
    COLLECT hash = d.shapeHash.shapeHash WITH COUNT INTO c
    FILTER c > 1
    SORT c DESC
    LIMIT 10
    RETURN {hash: hash, count: c}
'''):
    print(f'  {row["hash"]}: {row["count"]}')

print("\n=== TOP 10 VALUE-FINGERPRINT GROUPS (CANDIDATES) ===")
for row in db.aql.execute('''
  FOR d IN decls
    FILTER d.valueFingerprint != null
    COLLECT hash = d.valueFingerprint.shapeHash WITH COUNT INTO c
    FILTER c > 1
    SORT c DESC
    LIMIT 10
    RETURN {hash: hash, count: c}
'''):
    print(f'  {row["hash"]}: {row["count"]}')

print("\n=== SORRY/INFRASTRUCTURE DECLARATIONS ===")
for doc in db.aql.execute('''
  FOR d IN decls
    FILTER d.attrs != [] AND (POSITION(d.attrs, "infrastructure") != null OR POSITION(d.attrs, "sorry") != null)
    RETURN {name: d.name, kind: d.kind, module: d.module, attrs: d.attrs}
'''):
    print(f'  {doc["name"]} ({doc["kind"]}) | {doc["attrs"]}')

print("\n=== EDGE VALIDATION ===")
total = db.collection('edges').count()
valid = 0
for e in db.aql.execute('''
  FOR e IN edges
    LET from_doc = DOCUMENT(e._from)
    LET to_doc = DOCUMENT(e._to)
    FILTER from_doc != null AND to_doc != null
    RETURN 1
'''):
    valid += 1
print(f'Total edges: {total}, Valid edges: {valid}, Orphaned: {total - valid}')

print("\n=== DONE ===")
PYEOF
```

---

## Phase 6: CI Integration (GitHub Actions Example)

The build step below is for an isolated clean CI runner, not for an in-place
refresh of the persistent repository workspace.  Local refreshes must use the
cache-preserving Phase 2 command above.  CI must still index the full
`InfoGeometry.All` / `InfoGeometry` graph.

```yaml
# .github/workflows/decl-graph.yml
name: Declaration Graph Refresh

on:
  schedule:
    - cron: '0 2 * * *'  # Daily at 2 AM
  push:
    paths:
      - 'lean/**/*.lean'
      - 'lakefile.lean'

jobs:
  refresh-decl-graph:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install Lean
        uses: leanprover/lean4-action@v2
      - name: Build dagIndexer
        run: lake build dagIndexer
      - name: Start ArangoDB
        run: docker run -d -p 8530:8529 -e ARANGO_ROOT_PASSWORD=${{ secrets.ARANGO_PASSWORD }} arangodb/arangodb:3.11
      - name: Stream to ArangoDB
        env:
          ARANGO_PASSWORD: ${{ secrets.ARANGO_PASSWORD }}
        run: |
          python3 tools/infra/refresh_decl_graph.py \
            --stream \
            --import-root InfoGeometry.All \
            --namespace InfoGeometry \
            --arango-db infogeometry
      - name: Run Verification Queries
        run: |
          python3 tools/infra/arango_causal_memory.py \
            --database infogeometry query '
          LET declCount = LENGTH(decls)
          LET edgeCount = LENGTH(edges)
          LET orphanCount = LENGTH(
            FOR e IN edges
              LET from_doc = DOCUMENT(e._from)
              LET to_doc = DOCUMENT(e._to)
              FILTER from_doc == null OR to_doc == null
              RETURN 1
          )
          RETURN {
            decls: declCount,
            edges: edgeCount,
            orphans: orphanCount
          }
          '
```

---

## Key AQL Patterns Reference (CORRECTED)

| Search Type | AQL Pattern |
|-------------|-------------|
| ShapeHash equivalence | `COLLECT hash = d.shapeHash.shapeHash WITH COUNT INTO c` |
| ValueFingerprint equivalence | `COLLECT hash = d.valueFingerprint.shapeHash WITH COUNT INTO c` |
| Attribute filter | `FILTER d.attrs != [] AND POSITION(d.attrs, "tag") != null` |
| Module filter | `FILTER d.module == "InfoGeometry.Core"` |
| Kind filter | `FILTER d.kind == "theorem"` |
| Edge traversal (callers) | `FOR e IN edges FILTER e._to == "decls/key" LET src = DOCUMENT(e._from) RETURN src` |
| Edge traversal (callees) | `FOR e IN edges FILTER e._from == "decls/key" LET dst = DOCUMENT(e._to) RETURN dst` |
| Edge validation | `LET from_doc = DOCUMENT(e._from) LET to_doc = DOCUMENT(e._to) FILTER from_doc != null AND to_doc != null` |
| Document lookup | `DOCUMENT("decls/key")` |
| ShapeHash filter | `FILTER d.shapeHash.shapeHash == "3892707284033108221"` |

---

## Troubleshooting

| Issue | Fix |
|-------|-----|
| `python-arango not installed` | `pip install python-arango` |
| `dagIndexer` executable absent | Use the direct Lean runner supported by `refresh_decl_graph.py`; schedule any required build separately rather than rebuilding during refresh |
| `object file .olean does not exist` | Stop the refresh and repair the pinned cache separately; do not run `lake update` as part of ASTAQLHASH refresh |
| `could not execute external process` | Check `.lake/build/bin/dagIndexer` exists |
| ArangoDB connection refused | Ensure ArangoDB running on port 8530 |
| `object file InfoGeometry/All.olean does not exist` | Stop and restore/build the pinned `InfoGeometry.All` cache as a separate, sequential maintenance task before restarting refresh |
| `python-arango not installed` in lake env | Use `lake env pip install python-arango` |

---

## Files Modified in This Methodology

| File | Purpose |
|------|---------|
| `lean/DAG/Indexer.lean` | Owns streamed `DeclNode` / `StreamDecl` JSONL with fingerprints and edges |
| `lean/DAG/ExprFingerprint.lean` | Owns `ExprFingerprint` and `computeFingerprint` |
| `lean/DAG/SearchByHash.lean` | Native Lean-side shape-hash search over imported modules |
| `tools/infra/refresh_decl_graph.py` | Owns `--stream` mode with ArangoDB import |
| `tools/infra/hash_owner_map.py` | Native/offline shape-hash owner lookup and source owner scan |
| `tools/infra/aql/aql_functorial_bridge.py` | Adds `lean_decl`/`lean_status` provenance fields in the AQL functorial bridge lane |

---

This methodology gives you **constant-memory** declaration graph indexing with
**hash-based structural search** capability.

---

## Audit record

Audit results are **only valid for the checkout they were run against**, and must be
re-run rather than copied forward. A count quoted without its commit, its command,
and its scope is not evidence.

### What this document does *not* assert

- It does not assert that any named audit currently passes. The numbers below are
  historical records tied to a specific checkout, retained for provenance.
- It does not assert that the live graph matches the working tree. Graph freshness
  must be established from metadata at query time; a populated `decls` collection
  proves only that *some* refresh ran, not that it matches HEAD.
- `hash_owner_map.py` output, AQL clusters, and structural-vacuity results are
  **navigation evidence**. They never establish a theorem, an equivalence, or a
  closure.

### Reproducing an audit

Run the tools against the current checkout and record commit + date + scope:

```bash
git rev-parse HEAD
python3 tools/infra/axiom_audit.py
python3 tools/infra/arango_structural_vacuity_audit.py
python3 tools/infra/check_hollow_theorems.py
```

Note that `axiom_audit.py` counts `sorry`/`admit`/`axiom` **declarations**. It does
not detect the separate failure mode where a theorem is stated as a field of a
`structure` and then "proved" by `rw [thatField]` — that is an assumption, not a gap,
and it is invisible to a token count. For that, group by
`valueFingerprint.shapeHash` per the strict execution order above and read the owner
files.

### Historical record (2026-07-04 checkout)

Recorded for provenance only; superseded by any later run.

| Audit | Reported result |
|---|---|
| `axiom_audit.py` | 257 open gaps reported for that checkout |
| `arango_structural_vacuity_audit.py` | 0 findings |
| `check_hollow_theorems.py` | 0 findings |

Treat "0 findings" from the latter two as *absence of detected instances*, not as a
proof of soundness: both tools detect specific structural signatures and cannot see
an assumption smuggled in through a `Prop`-valued structure field.
