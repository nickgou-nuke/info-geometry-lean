# Expr Alpha Dedup Report

- generated_at: `2026-04-18T10:48:42Z`
- input_dir: `artifacts/expr-graph/arango-smoke`
- const_mode: `normalize`

## Compression Summary

- decl_nodes: `185`
- expr_nodes: `9657`
- unique_expr_fingerprints: `1620`
- expr_dedup_factor: `5.961111`
- declarations_with_roots: `50`
- unique_decl_fingerprints: `44`
- decl_dedup_factor: `1.136364`

## Declaration Equivalence Groups

| rank | group_size | fingerprint | declarations |
|---|---:|---|---|
| 1 | 3 | `aa86380e9dc587bc` | DAG.buildGraphFromEnv.match_1, DAG.buildGraphFromEnv.match_3, DAG.buildGraphFromEnv.match_7 |
| 2 | 2 | `246fea71e8522f9b` | DAG.EdgeKind.type.sizeOf_spec, DAG.EdgeKind.value.sizeOf_spec |
| 3 | 2 | `a2ac12c8e56b8df3` | DAG.EdgeKind.casesOn, DAG.EdgeKind.recOn |
| 4 | 2 | `a822237b58d52905` | DAG.Graph.ctorIdx, DAG.HydratedGraph.ctorIdx |
| 5 | 2 | `aa40c70cb655e218` | DAG.Graph, DAG.HydratedGraph |

## Repeated Subgraphs

| rank | expr_tag | occurrences | declarations | fingerprint |
|---|---|---:|---:|---|
| 1 | `const` | 2735 | 49 | `b6c7332d05f22091` |
| 2 | `bvar` | 254 | 46 | `1d1a61f3b7f94cf8` |
| 3 | `bvar` | 247 | 43 | `302cf5c3a6a58359` |
| 4 | `bvar` | 205 | 38 | `1fd008828a35604a` |
| 5 | `app` | 571 | 37 | `bdf276339b3e06c3` |
| 6 | `app` | 79 | 37 | `18821c250af614cc` |
| 7 | `app` | 67 | 31 | `1c929ac80a235e03` |
| 8 | `sort` | 74 | 28 | `758a52718f890c41` |
| 9 | `bvar` | 150 | 27 | `2481657b85146575` |
| 10 | `app` | 60 | 26 | `86c3825f1d232b9d` |
| 11 | `app` | 52 | 21 | `7792bba688de3ef3` |
| 12 | `app` | 52 | 21 | `7a81e1cf0b3151f0` |

