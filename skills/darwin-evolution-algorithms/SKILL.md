---
name: darwin-evolution-algorithms
description: Use when running genuine graph algorithms over the live Darwin commit-evolution and declaration-DNA graphs — Tarjan SCC, union-find components, DNA cohorts, Linnaean rank hierarchy, and Lean-mirrored data invariants.
metadata:
  short-description: Read-only graph algorithms over commit lineage and DNA
tags:
  - arango
  - darwin
  - evolution
  - graph-algorithms
  - scc
  - dna-cohorts
  - rank-hierarchy
related_skills:
  - darwin-commit-taxonomy
  - astaqlhash-concept-bridge
---

# Darwin Evolution Algorithms

Use this skill to run genuine graph algorithms over the live Darwin
commit-evolution graph stored in ArangoDB. This module is **read-only** — no
inserts, replacements, or truncates on any collection.

## Algorithms implemented

| Algorithm | What it computes |
|-----------|------------------|
| Tarjan SCC | Strongly-connected components over the commit lineage DAG; proves acyclicity when every SCC is a singleton |
| Union-find weak components | Connected components of the undirected lineage graph |
| SCC condensation | Coarsens the DAG by contracting SCCs; reports component count, condensation edges, top sizes |
| DNA cohorts | Bipartite union-find over commits and shared declarations via `commit_decl_edges`; two commits are in one cohort when they bridge to a shared declaration |
| Linnaean rank hierarchy | Per-rank commit histogram, distinct taxa per rank, parent→child rank-index delta histogram |
| Lean-mirrored invariants | Round-trip check `taxonRankIndex == _rank_index(taxonRank)`; anti-collapse witnesses (distinct commits sharing identical `modulePaths`) |

## Command

```bash
PYTHONPATH=/home/goutev/repos/info-geometry-lean \
  ARANGO_DATABASE=darwin_commits \
  ARANGO_PASS=<password> \
  /home/goutev/miniforge3/envs/sage/bin/python \
  tools/infra/darwin_evolution_algorithms.py \
  --json-out artifacts/dag/darwin_evolution_report.json
```

The command:

1. Connects to ArangoDB using the repository environment loader
2. Fetches the commit lineage (vertices + `parent_of` adjacency)
3. Runs iterative Tarjan SCC (no recursion limit)
4. Computes condensation-DAG statistics
5. Computes undirected weak components via union-find
6. Builds DNA cohorts from `commit_decl_edges` (if present)
7. Computes the Linnaean rank hierarchy and descent deltas
8. Checks Lean-mirrored data invariants (rankIndex round-trip, anti-collapse witnesses)
9. Writes a JSON report to `--json-out` (default `artifacts/dag/darwin_evolution_report.json`)
10. Prints a human-readable summary to stdout

## Output schema

The JSON report uses schema `info_geometry.darwin_evolution_report.v1` and contains:

- `reportSchema`, `generatedAt`, `repoCommit`, `database`, `endpoint`, `sourceAuthority`
- `lineage`: commit node count, parent_of edge count, SCC stats, lineage acyclic flag, weak component stats
- `dnaCohorts`: distinct cohorts, commit→decl edge count, cohort size histogram, largest cohorts
- `taxonomy`: rank histogram, parent→child delta histogram, rank increase/flat/decrease edge counts
- `leanMirroredInvariants`: rankIndex round-trip violations, anti-collapse witness count and examples

## Interpretation

- **Lineage acyclic**: if `componentCountMultiNode == 0`, the git lineage DAG is proven acyclic — every SCC is a singleton
- **DNA cohorts**: groups commits that touch shared declarations; useful for finding commits that co-evolved on the same Lean declarations
- **Rank increase/decrease edges**: tracks Linnaean rank transitions across parent→child edges; rank increases indicate speciation events
- **Anti-collapse witnesses**: distinct commits sharing identical `modulePaths` remain distinct node keys — this is inhabited by real data, not vacuous

## Authority boundary

- All results are **navigation evidence only**, valid for the checkout recorded in the report
- Graph paths and fingerprints do not prove mathematical statements
- Lean owner files decide truth; graph tools are descent planners and mass locators
- The command is read-only: it never inserts, replaces, or truncates any collection

## Example session

```bash
cd /home/goutev/repos/info-geometry-lean
PYTHONPATH=/home/goutev/repos/info-geometry-lean \
  ARANGO_DATABASE=darwin_commits \
  ARANGO_PASS=alexandria_root \
  /home/goutev/miniforge3/envs/sage/bin/python \
  tools/infra/darwin_evolution_algorithms.py \
  --json-out artifacts/dag/darwin_evolution_report.json
```

Sample output:

```
=== DARWIN EVOLUTION REPORT ===
repo commit : 028bc203a  db: darwin_commits
lineage     : 13682 commits, 14008 parent_of edges
lineage acyclic (no multi-node SCC): True
SCC         : 13682 components, largest=1, condensation edges=14008
weak comps  : 1 (largest 13682, singletons 13682)
DNA cohorts : <N> cohorts from <N> commit->decl edges (largest <N>)
rank histogram:
  Domain  (idx 0):      0 commits,     0 distinct taxa
  Kingdom (idx 1):    <N> commits,   <N> distinct taxa
  ...
descent deltas: +<N> increases, <N> flat, <N> decreases
invariants  : rankIndex round-trip violations=0 | anti-collapse witnesses=<N>
json report: artifacts/dag/darwin_evolution_report.json
```
