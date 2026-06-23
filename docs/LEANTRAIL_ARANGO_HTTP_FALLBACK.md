# LeanTrail Arango HTTP fallback

This note records the Arango query path recovered from `/home/goutev/auto`.

Primary references in the legacy tree:

- `/home/goutev/auto/proofs/tools/lean_graph/README.md`
  - Lean syntax/environment bridge workflow.
  - Arango collections such as `lean_decls`, `syntax_nodes`, `references`,
    `ast_child`, `has_syntax` for the GEPA graph.
- `/home/goutev/auto/proofs/scripts/aql_queries.md`
  - AQL query arsenal for dependency cones, sockets, AST sorry scans, and
    syntax/environment bridge coverage.
- `/home/goutev/.config/arango/env.sh`
  - Runtime connection variables:
    `ARANGO_URL`, `ARANGO_ENDPOINT`, `ARANGO_DATABASE`, `ARANGO_DB`,
    `ARANGO_USERNAME`, `ARANGO_USER`, `ARANGO_PASSWORD`.
- `/tmp/aql_query.py`
  - Temporary direct HTTP `_api/cursor` wrapper used when `python-arango` is not
    installed in the active Python environment.

`tools/leantrail/aql_query.py` is the promoted dependency-light AQL runner. It
uses the same HTTP `_api/cursor` path and reads `~/.config/arango/env.sh`
automatically when process environment variables are not already set:

```bash
tools/infra/with_arango_env.sh -- lake script run leantrailAQLQuery 'RETURN 1'
```

`tools/leantrail/arango_dump.py` also implements this fallback directly for
graph dumps and cones. In this repository the default collections are
`dag_nodes`/`dag_edges`, so the zero-configuration command works locally:

```bash
lake script run leantrailArangoDump \
  --out /tmp/leantrail_arango_dump.json
```

Equivalent explicit invocation:

```bash
lake script run leantrailArangoDump \
  --collection dag_nodes \
  --edges dag_edges \
  --out /tmp/leantrail_arango_dump.json
```

If `python-arango` is importable, the tool uses it.  Otherwise it POSTs AQL to:

```text
$ARANGO_ENDPOINT/_db/$ARANGO_DATABASE/_api/cursor
```

with Basic auth from the same environment variables.

Causal-cone seeds may be full Arango `_id`s or declaration names/keys in the
node collection:

```bash
lake script run leantrailArangoDump \
  --cone-downstream 'InfoGeometry.Algebra.AlbertCD.CDInvolutionDatum.casesOn' \
  --max-depth 1 \
  --out /tmp/leantrail_cone.json
```

For this repository's current local Arango instance, the available graph-shaped
collections include `dag_nodes`/`dag_edges`, `syntax_nodes`/`ast_child`, and raw
InfoTree collections.  The old auto docs' `lean_decls`/`references` names are
valid for the GEPA import schema but may not exist in every database snapshot;
pass the collection names explicitly when querying an older GEPA database.

## Full syntax dump + HTTP ingest workflow

This repo now has the same stdlib-only syntax-AST path as `/home/goutev/auto`,
under `tools/leantrail/`:

```bash
# 1. Lean-native syntax dump
lake env lean --run tools/leantrail/DumpLeanGraph.lean \
  lean/InfoGeometry/Algebra/CuntzLorentzPoincarePresentation.lean \
  > /tmp/cuntz_lorentz_syntax.jsonl

# 2. Shape validation
python3 tools/leantrail/check_dump_shape.py --expect-keyword theorem \
  < /tmp/cuntz_lorentz_syntax.jsonl

# 3. Dry-run ingest validation
python3 tools/leantrail/ingest_syntax_to_arango.py /tmp/cuntz_lorentz_syntax.jsonl

# 4. HTTP ingest without python-arango
python3 tools/leantrail/ingest_syntax_to_arango.py \
  /tmp/cuntz_lorentz_syntax.jsonl \
  --execute-http

# 5. Query with stdlib-only AQL runner
python3 tools/leantrail/aql_query.py <<'AQL'
FOR d IN syntax_decls
  FILTER CONTAINS(d.name, 'CuntzLorentzPoincarePresentation')
  SORT d.name
  LIMIT 20
  RETURN {name: d.name, keyword: d.keyword, range: d.range}
AQL
```

The local AQL smoke test is:

```bash
bash tools/leantrail/aql_smoke_test.sh
```

## Repo smoke test

Run the full local non-LLM LeanTrail smoke path:

```bash
tools/infra/with_arango_env.sh -- lake script run leantrailSmoke
```

This checks:

- `ast_extract.py` on `lean/InfoGeometry/Algebra`, including Arango-ready
  `_key`, `_from`, `_to`, module, and namespace fields;
- `external_index.py --repo lean/InfoGeometry/Algebra --format arango`, without
  requiring an external directory;
- `oracle_search.py --local-only`, proving search is grounded in actual local
  declarations before any remote oracle call;
- `arango_dump.py` causal-cone lookup by declaration name against the local
  `infogeometry.dag_nodes/dag_edges` graph;
- `ast_aql_optimize.py --no-index`, confirming optimized AST AQL smoke queries
  against `syntax_nodes`/`ast_child`.

Use `--skip-arango` if the local Arango service is not running:

```bash
lake script run leantrailSmoke --skip-arango
```

## AST AQL optimization

The AST graph is large enough that declaration-first deep traversals can be slow.
Use indexed, atom-first queries for GEPA scans:

```bash
tools/infra/with_arango_env.sh -- lake script run leantrailAstAQLOptimize
```

This creates/ensures persistent indexes on:

- `syntax_nodes.declName`
- `syntax_nodes.value`
- `syntax_nodes.raw`
- `syntax_nodes.syntaxKind`
- `syntax_nodes.nodeKind`
- `syntax_nodes.(declName,path)`
- `syntax_decls.name`
- `syntax_decls.keyword`

Current live smoke on this repo reports roughly:

```text
syntax_nodes: 246213
ast_child:    241030
syntax_decls: 5194
decl_root:    5194
atom_first_sorry_scan: 0.001s
atom_first_tactic_scan: 0.002s
bounded_decl_ast_cone: 0.001s
```
