---
name: darwin-commit-taxonomy
description: Use when querying the Darwin commit-evolution taxonomy in ArangoDB — read-only operators over commit_nodes/commit_edges/taxonomy_ranks plus bridges to decls DNA.
metadata:
  short-description: Read-only commit phylogeny and decl-DNA bridge queries
tags:
  - arango
  - darwin
  - taxonomy
  - phylogeny
  - commit-graph
  - dna-bridge
related_skills:
  - darwin-evolution-algorithms
  - astaqlhash-concept-bridge
---

# Darwin Commit Taxonomy

Use this skill to run read-only phylogenetic and taxonomic queries over the
Darwin commit-evolution graph stored in ArangoDB (`darwin_commits` database).
The graph holds `commit_nodes`/`commit_edges` (repository history as an
evolutionary taxonomy) and `commit_decl_edges` (causal links from commits to
declaration DNA nodes). All queries are read-only.

## Prerequisites

- ArangoDB running at `http://127.0.0.1:8530` (endpoint from `configs/local/hive_arango.env`)
- Sage Python environment: `/home/goutev/miniforge3/envs/sage/bin/python`
- `python-arango` package installed in that environment
- Env file `configs/local/hive_arango.env` present with `ARANGO_ENDPOINT`, `ARANGO_DATABASE`, `ARANGO_USER`, `ARANGO_PASS`

## Rank ontology

Linnaean ranks are assigned per commit based on message and paths:

| Rank | Index | Heuristic |
|------|-------|-----------|
| Domain | 0 | (reserved) |
| Kingdom | 1 | merge commits / multiple parents |
| Phylum | 2 | `lean/InfoGeometry/` paths, ≥3 paths |
| Class | 3 | module-path prefix `lean/InfoGeometry/<subdir>/` |
| Order | 4 | message contains `feat`, `fix`, `refactor`, `formalize` |
| Family | 5 | message contains `archetype`, `theorem`, `lemma` |
| Genus | 6 | exactly one path |
| Species | 7 | default |

## Available queries

### `taxonomy_summary`

List every taxonomy rank with commit count, sorted by `rankIndex`:

```bash
PYTHONPATH=/home/goutev/repos/info-geometry-lean \
  ARANGO_DATABASE=darwin_commits \
  ARANGO_PASS=<password> \
  /home/goutev/miniforge3/envs/sage/bin/python \
  tools/infra/darwin_commit_taxonomy.py --query taxonomy_summary
```

### `species_emergence`

List commits of a given rank, sorted by date:

```bash
... tools/infra/darwin_commit_taxonomy.py --query species_emergence --rank Species
```

### `commit_scc`

Run Tarjan SCC over the commit lineage DAG. In a linear git history every SCC
is a singleton; this command *proves* lineage acyclicity by finding no
multi-node SCC:

```bash
... tools/infra/darwin_commit_taxonomy.py --query commit_scc
```

### `coarse_grain`

Group commits by rank and count per taxon label:

```bash
... tools/infra/darwin_commit_taxonomy.py --query coarse_grain --rank Family
```

### `phylogenetic_paths`

Trace inbound ancestral paths up to `--depth` from a target commit:

```bash
... tools/infra/darwin_commit_taxonomy.py \
  --query phylogenetic_paths \
  --target <commit_sha> \
  --depth 6
```

### `verified_species`

List commits flagged `leanVerified` with rank, date, and message:

```bash
... tools/infra/darwin_commit_taxonomy.py --query verified_species
```

### `commit_decl_bridge`

Sample commit → declaration DNA bridge edges (commit → decl key):

```bash
... tools/infra/darwin_commit_taxonomy.py --query commit_decl_bridge --limit 200
```

### `connected_components`

List commits touching a module prefix with their module paths:

```bash
... tools/infra/darwin_commit_taxonomy.py \
  --query connected_components \
  --module-prefix lean/InfoGeometry/
```

## Authority boundary

- Graph results are **navigation evidence only** — they do not prove mathematical statements.
- Lean kernel-checked source files decide truth; graph tools are descent planners.
- Never write to `decls`, `edges`, or `raw_infotree_*` collections. Write only to `commit_*` collections if ingesting.
- Do not guess credentials; use `configs/local/hive_arango.env`.

## Example session

```bash
cd /home/goutev/repos/info-geometry-lean
PYTHONPATH=/home/goutev/repos/info-geometry-lean \
  ARANGO_DATABASE=darwin_commits \
  ARANGO_PASS=alexandria_root \
  /home/goutev/miniforge3/envs/sage/bin/python \
  tools/infra/darwin_commit_taxonomy.py \
  --query taxonomy_summary
```

Expected output: one JSON object per taxonomy rank with `rank`, `rankIndex`, `name`, `commits` fields.
