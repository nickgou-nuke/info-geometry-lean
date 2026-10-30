---
name: darwin-evolution-algorithms
description: Run read-only graph algorithms over Git commit ancestry and the commit-to-declaration navigation bridge.
metadata:
  short-description: Read-only ancestry, cohort, and weak-facet analyses
tags:
  - arango
  - darwin
  - evolution
  - graph-algorithms
  - scc
  - dna-cohorts
related_skills:
  - darwin-commit-taxonomy
  - astaqlhash-concept-bridge
---

# Darwin Evolution Algorithms

The algorithms read the Arango Darwin commit graph and emit navigation
reports. Git parent edges represent repository ancestry. Optional
`commit_decl_edges` connect commits to current declaration records under their
own resolution label; they are not historical declaration snapshots.

## Analyses

| Analysis | Evidence |
|---|---|
| Tarjan SCC | SCCs in the imported parent-edge graph; singleton SCCs are an observed data result, not an independently proved Git invariant |
| Weak components | Undirected connected components of imported parent edges |
| SCC condensation | Component sizes and edges between observed components |
| Declaration cohorts | Bipartite connectivity induced by `commit_decl_edges`; inherits each edge's resolution limits |
| Change facets | Multi-label weak categories with coverage and malformed-row counts; no rank order |
| Commit identity witnesses | Distinct commit keys sharing one non-empty `modulePaths` list |

## Command

```bash
PYTHONPATH=/home/goutev/repos/info-geometry-lean \
  /home/goutev/miniforge3/envs/sage/bin/python \
  tools/infra/darwin_evolution_algorithms.py \
  --json-out artifacts/dag/darwin_evolution_report.json
```

The command reads ArangoDB, computes the listed graph summaries, and writes
the report locally. It performs no database writes.

## Report

Schema: `info_geometry.darwin_evolution_report.v2`.

- `lineage`: imported commit and parent-edge counts, SCC/condensation and weak
  component statistics;
- `dnaCohorts`: observed commit/declaration connectivity, if the bridge exists;
- `changeFacets`: `weak-rule-v3` category counts, coverage, malformed labels,
  and legacy rank-row count; rule weights are not probabilities;
- `commitIdentityWitnesses`: distinct-key witnesses for equal non-empty path
  lists and the count of legacy rank rows.

## Interpretation limits

- Graph calculations describe the imported graph and its recorded provenance.
- Acyclic-looking SCC output does not prove the source repository history is
  complete; omitted refs or missing edges change that graph.
- Shared declaration cohorts inherit the current-census bridge limitation.
- Similar fingerprints, path overlap, and weak categories do not prove that a
  theorem changed, that two declarations are equivalent, or that one commit
  descends semantically from another.
- Lean owner source and kernel checks decide formal truth.
