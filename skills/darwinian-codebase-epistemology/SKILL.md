---
name: darwinian-codebase-epistemology
description: Track code and declaration lineage with repository graph tools, test graph coverage against Git, and ground inferred archetypes in Lean owner declarations.
---

# Darwinian Codebase Epistemology

Use when treating commits, declarations, term fingerprints, or dependency
graphs as a lineage/evolution dataset. “DNA,” “ancestry,” and “phylogeny” are
working metaphors for explicit data fields and algorithms; do not promote them
to biological or mathematical claims without a defined model.

## Keep the lineage layers separate

- **Git ancestry:** commit vertices and parent edges from Git itself.
- **Declaration dependency:** Lean declarations and references extracted from
  compiler/source data.
- **Term fingerprints:** versioned structural digests with a documented
  encoding and open-term policy.
- **Inferred affinity/tree:** a model-dependent result over comparable
  markers; it is not the recorded parent relation.

An edge in one layer is not automatically an edge in another. A merge commit
records Git parents, not semantic inheritance of each theorem. A shared
declaration marker is not proof that two commits are ancestor/descendant.

## Run and audit the repository tools

Inspect each tool's current CLI and schema before execution. Relevant owners
include:

- `tools/infra/darwin_evolution_algorithms.py` for read-only Arango commit and
  commit/declaration graph summaries;
- `tools/infra/darwin_commit_graph.py` and
  `tools/infra/darwin_commit_taxonomy.py` for the adjacent Git/taxonomy lanes;
- `tools/infra/arango_expr_graph_ingest.py` for expression/de Bruijn graph
  ingestion;
- `tools/quality/counterexample_inventory.py` for lexical candidate discovery.

For any Arango-derived report, record checkout SHA, database/collection names,
vertex and edge counts, extraction time/version where available, and the
matching local Git counts. Compare at least commit vertices and parent edges
against `git rev-list --count` and `git rev-list --parents --all` (or the
tool's documented exact scope). If a graph has vertices but zero expected
parent edges, or a large coverage mismatch, mark that projection incomplete;
do not interpret singleton cohorts or empty clades as a substantive result.

Use `docs/ASTAQLHASH-HOWTO.md`,
`docs/ARANGO_DAG_REFRESH_METHODOLOGY.md`, and
`docs/REPO_DEEP_SEARCH_PROTOCOL.md` for provenance, refresh, and descent from
graph candidates to Lean owners. Prefer the current local DAG index and
LeanTrail where those are the maintained lane. Treat stale Arango projections,
generated reports, fingerprints, and graph algorithms as navigation evidence.

For fingerprint-based trees, verify the marker grain, version compatibility,
missingness policy, and source of each state before calculating distances.
Cryptographic digest inequality is a categorical mismatch, not a mutation
count or metric distance unless a separately justified model defines it. Do
not infer a root, historical ancestor, time scale, or confidence from an
unrooted affinity tree without corresponding model assumptions and evidence.

## From graph candidate to formal claim

1. Preserve source/report provenance and the exact graph query or command.
2. Check data coverage and distinguish missing edges from genuine absence.
3. Extract a candidate relationship without assigning its mathematical
   meaning from labels, hashes, rank, or proximity.
4. Descend to the current Lean declarations; read carriers, definitions,
   theorem statements, proof bodies, imports, and dependents.
5. State the smallest explicit map/compatibility theorem that would connect
   the structures. If none is proved, report a candidate bridge or open debt.
6. Only kernel-checked owner declarations promote formal truth. A graph score,
   cohort, hash match, successful ingest, or generated narrative never does.

When the task is a proof repair, route the resulting formal claim through
`skills/epistemic-compilation/SKILL.md`; when a failed identity yields a
residual operator, use `skills/anomaly-resolution/SKILL.md`.
