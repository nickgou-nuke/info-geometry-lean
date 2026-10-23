# Quarantine: pre-`bc151ec08` declaration-graph indexer code

> Status: `quarantined` — do not build, run, import, or copy from this folder.
> Quarantined: 2026-10-22. Files carry a `.lean.quarantined` suffix so Lake,
> `lean --run`, and `*.lean` globbing tools ignore them.

## Why

The live ArangoDB declaration graph (`http://127.0.0.1:8530`, database
`infogeometry`, collections `decls` / `edges`) was written by this old code
version, not by the current `lean/DAG/Indexer.lean`.

Evidence (read-only, 2026-10-22):

| Check | Result |
|---|---|
| Live `decls` attributes | `name, kind, module, file, line, column, doc, attrs, typeFingerprint, valueFingerprint, shapeHash` |
| `canonicalTypeHash` / `canonicalValueHash` / `dagShapeHash` on live rows | absent |
| `valueFingerprint.algorithmVersion` on live rows | null for all 171,308 rows |
| `DeclNode` in `e5e14fc61:lean/DAG/Indexer.lean` | exactly the 11 live fields above |
| `ExprFingerprint` in `e5e14fc61:lean/DAG/ExprFingerprint.lean` | no `algorithmVersion` field |
| Commit that added `canonical*`, `dagShapeHash`, `algorithmVersion` | `bc151ec08` (2026-09-10) |
| Current `lean/DAG/Indexer.lean` (lakefile `lean_exe dagIndexer`, root `DAG.Indexer`) | emits the canonical fields |

`e5e14fc61` is the parent of `bc151ec08`, i.e. the last revision of the old
record shape.

## Contents

| File | Source | Notes |
|---|---|---|
| `DAG_Indexer.e5e14fc61.lean.quarantined` | `git show e5e14fc61:lean/DAG/Indexer.lean` | producer of the live row shape (md5 `7dff087d…`) |
| `DAG_ExprFingerprint.e5e14fc61.lean.quarantined` | `git show e5e14fc61:lean/DAG/ExprFingerprint.lean` | fingerprint without `algorithmVersion` |
| `scripts_Indexer.212e57e86.lean.quarantined` | `git mv scripts/Indexer.lean` | older ancestor (no fingerprints); was unreferenced and not a Lake target |
| `scripts_ExportDecls.212e57e86.lean.quarantined` | `git mv scripts/ExportDecls.lean` | older `DeclRow` exporter; only self-referenced |

## Left in place on purpose

- `lean/DAG/Indexer.lean`, `lean/DAG/ExprFingerprint.lean`: current owners.
- `lean/DAG/DeclIndex.lean`: current; imported by `DAG.ConeCommand` and `DAG.WittenIndexCommand`.
- `lean/DAG/ExportDecls.lean`: separate legacy inventory exporter (`DeclRow`), not a `decls`/`edges` producer.
- Untracked snapshot copies of older indexer versions (not moved, to avoid touching
  backup/recovery areas): `src/infogeometry/lean/DAG/{Indexer,ExportDecls,DeclIndex}.lean`,
  `reports/cleanup-loop/2026053*/iter-001-snapshot/lean/DAG/*`,
  `artifacts/upstream_snapshot/all_sources/scripts/{Indexer,ExportDecls}.lean`.
- The live `infogeometry.decls` / `edges` data: unchanged. Refreshing it with the
  current indexer is a separate, authorized step (`refresh_decl_graph.py --stream`
  truncates the live collections; `--generation-id` writes new collections).
- `.github/workflows/build_thesis.yml` line 73 references `lean/scripts/ExportDecls.lean`,
  a path that does not exist; not changed here.

## Restore

`git mv` the two `scripts_*` files back and drop the suffix; the `DAG_*` files
are recoverable at any time with `git show e5e14fc61:<path>`.
