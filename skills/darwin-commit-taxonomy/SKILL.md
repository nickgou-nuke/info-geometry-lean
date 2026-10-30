---
name: darwin-commit-taxonomy
description: Query Git commit ancestry and evidence-bearing weak change-category facets in ArangoDB.
metadata:
  short-description: Read-only Git ancestry and multi-label change facets
tags:
  - arango
  - darwin
  - evolution
  - commit-graph
  - weak-classification
  - dna-bridge
related_skills:
  - darwin-evolution-algorithms
  - astaqlhash-concept-bridge
---

# Darwin Commit History and Change Facets

Use this skill for read-only queries over the Darwin commit graph in ArangoDB.
`commit_nodes` and `commit_parent_edges_v2` represent Git commits and ordered,
parent-to-child Git relations. Each current commit record may also carry `changeLabels`, a
multi-label weak classification derived from commit subject and changed paths.
Categories are non-hierarchical. They are not species, ancestors, declaration
identities, or theorem-status claims.

## Prerequisites

- ArangoDB endpoint and credentials from `configs/local/hive_arango.env`.
- Sage Python environment: `/home/goutev/miniforge3/envs/sage/bin/python`.
- `python-arango` installed in that environment.
- Use the repository Arango environment loader; do not hard-code credentials.

## Category record

`changeLabels` rows use schema `info_geometry.commit_change_labels.v1` and
method `weak-rule-v3`. Each label contains:

- `category` and stable `categoryId`;
- `ruleWeightPercent`, an uncalibrated rule weight, not a probability;
- matched textual/path `evidence` and typed `evidenceKinds`;
- `status: "weak_rule"`.

No rank order is defined. A commit can have several categories. A path hint
does not establish that a particular declaration changed; the optional
commit-to-declaration bridge has its own resolution and evidence fields.

## Queries

All queries use the `darwin_commit_taxonomy.py` read-only interface:

```bash
PYTHONPATH=/home/goutev/repos/info-geometry-lean \
  /home/goutev/miniforge3/envs/sage/bin/python \
  tools/infra/darwin_commit_taxonomy.py --query taxonomy_summary
```

List commits carrying one weak category:

```bash
... tools/infra/darwin_commit_taxonomy.py \
  --query category_emergence --category "Bug Fix"
```

Group commit counts by category (or filter to one):

```bash
... tools/infra/darwin_commit_taxonomy.py --query coarse_grain
... tools/infra/darwin_commit_taxonomy.py \
  --query coarse_grain --category "Refactor/Restructure"
```

Other supported queries:

- `commit_scc`: Tarjan SCCs over the observed Git parent graph;
- `phylogenetic_paths --target <commit_sha> --depth 6`: traverse parent links;
- `commit_decl_bridge --limit 200`: inspect existing commit-to-declaration rows;
- `connected_components --module-prefix lean/InfoGeometry/`: list commits by
  path habitat.

`taxonomy_summary` retains its CLI name for continuity, but now returns
category counts with `hierarchy: false`. The old `species_emergence`,
`verified_species`, and rank-index queries have been removed: the prior importer
assigned biological ranks from unrelated message/path heuristics and set
`leanVerified` false for every row.

## Refresh and legacy data

To populate current `changeLabels`, rerun `tools/infra/darwin_commit_graph.py`
with the normal importer options after reviewing its write scope. It updates
only Darwin commit collections. Do not pass `--drop-existing` unless truncating
the owned commit collections is explicitly intended. The importer does not
delete the legacy `taxonomy_ranks` collection or edit declaration-DAG,
InfoTree, or `evo_*` collections. Legacy rank fields may remain in stored rows
until reimport; reports count them and exclude them from current facets.

## Authority boundary

- Git parent edges are the repository-history authority for ancestry.
- Category matches are weak classification evidence only; rule weights are
  not calibrated confidence.
- Declaration fingerprints and Arango graph joins are navigation evidence.
- Lean owner source and kernel-checked declarations decide formal truth.
- Do not use taxonomy labels to claim semantic change, theorem equivalence,
  biological descent, or verified Lean status.
