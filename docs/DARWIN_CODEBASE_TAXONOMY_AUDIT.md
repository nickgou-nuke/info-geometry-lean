# Darwin phylogeny and codebase taxonomy audit

**Status:** source audit and implementation plan
**Scope:** tracked Git/commit evolution, declaration-DNA, InfoTree, graph/Hodge,
and classification tooling, plus identified ignored worktree candidates,
inspected on 2026-10-28. This is not a claim that all mathematical owner
declarations or all Arango runtime rows were audited.

## Executive finding

The worktree contains multiple substantial, non-equivalent evolution-analysis
paths. Git tracking checks show that some advanced paths are ignored local
code, not committed repository infrastructure. Keep those provenance states
distinct before claiming or reusing them.

The offline `tools/repository_evolution` pipeline, promoted from ignored local
files in this task (it was not tracked at the audited `HEAD`):
`phylogeny_export.py` reads Git ancestry and consumes optional
`repo-dna-snapshots/v1` packets; `dna_character_tree.py` constructs a
descriptive structural-affinity tree from their fingerprints; `ancestry_hodge.py`
computes exact sparse graph-Hodge/cycle data on commit ancestry; and
`render_explorer.py` renders the phylogeny. Tests cover commit DAG/window
handling, provenance gates, structural-marker behavior, and rendering.

The tracked Arango Darwin path (`tools/infra/darwin_commit_graph.py`,
`darwin_commit_taxonomy.py`, `darwin_evolution_algorithms.py`) stores commit
history and optional commit/declaration links in `darwin_commits`. Its links
are resolved against the current `infogeometry.decls`, and its Linnaean rank
is heuristic. These links are useful navigation evidence, not historical
declaration snapshots or semantic species.

No producer for compiled, source-verified historical declaration-DNA packets
was found in the inspected tracked paths. This is a scoped worktree audit, not
proof of repository-wide absence. The candidate
`tools/infra/darwin_versioned_declarations.py` was removed after finding the
packet consumer found in ignored local code; it would have duplicated history-to-DNA work
with weaker, syntax-only evidence.

## Existing pipeline inventory

### Offline phylogeny and declaration DNA (promoted from ignored worktree code)

- `tools/repository_evolution/phylogeny_export.py`
  - Reads refs and reachable Git commit ancestry without replacing refs or
    using network access.
  - Preserves full commits while compressing display nodes and links; checks
    that expanded displayed links recover the original parent edges.
  - Consumes `repo-dna-snapshots/v1`; validates commit membership, unique
    generations and names, fingerprint schema/version, and source-verification
    manifest fields. It explicitly records that this is manifest-attested,
    **not independently verified by Lean compilation**.
- `tools/repository_evolution/dna_character_tree.py`
  - Accepts native declaration digest records and closed type/value digest
    markers. Exact qualified names are assumed alignments; no rename/homology
    inference is performed.
  - Produces an **unrooted structural-affinity** tree using categorical marker
    mismatch distances. It does not infer Git ancestry, theorem equivalence,
    or a molecular clock.
- `tools/repository_evolution/ancestry_hodge.py`
  - Uses the unfilled oriented commit graph 1-complex and exact sparse integer
    incidence/cycle certificates. Its contract excludes declaration
    phylogeny, triangle filling, and floating-point spectral inference.
- `tools/repository_evolution/render_explorer.py`
  - Renders the offline phylogeny and accepts an Hodge report only when its
    source digest matches the exact input bytes and its exact checks pass.
- Relevant tests: `tests/test_repository_phylogeny_export.py`,
  `tests/test_repository_dna_character_tree.py`,
  `tests/test_repository_evolution_render.py`.

Tracking check against `HEAD` before this task's staged addition:
`git ls-files` did not list `tools/repository_evolution/`, and
`.git/info/exclude` ignored that directory. The paths are being promoted in
the current task-scoped staged set; their former ignored status is provenance,
not a claim about the resulting index.

### Tracked Arango Darwin history and current-declaration bridge

- `tools/infra/darwin_commit_graph.py`
  - Imports commit nodes, parent edges, and heuristic rank records.
  - Optional `attach_decl_edges` parses declaration-looking added lines in
    diffs, then resolves names in the current `decls` collection. File/line/
    edge caps are supported; deleted or moved declarations may not resolve.
  - `--drop-existing` truncates Darwin commit collections and is destructive.
- `tools/infra/darwin_evolution_algorithms.py`
  - Reads the Arango commit graph for SCCs, connected components, rank
    histograms, shared-declaration cohorts, and data-level checks. The
    declaration cohorts reflect the current-declaration bridge, not
    declaration versions in each commit.
- `tools/infra/darwin_commit_taxonomy.py`
  - Provides read-only queries over the Darwin collections.
- `lean/InfoGeometry/Graph/DarwinCommitTaxonomy.lean`
  - Defines the rank/commit/edge data and proves rank-index facts. These types
    formalize a schema; they do not prove that heuristic commit labels are a
    correct semantic taxonomy.

The optional cross-database bridge and browser visualizer listed below are
ignored local files, not part of this tracked Arango baseline.

### Commit-change labels and dashboards

Tracking check against `HEAD` before this task's staged addition: the inspected
`tools/infra/evolution_*` and supplementary
`darwin_*` files (including `evolution_extract.py`, `evolution_taxonomy.py`,
`evolution_path_habitat.py`, `evolution_ingest.py`,
`darwin_phylogeny_pipeline.py`, `darwin_phylogeny_dashboard.py`,
`darwin_dna_bridge.py`, and `darwin_tree_visualizer.py`) are not listed by
`git ls-files`; the `evolution_*` files are explicitly ignored by
`.git/info/exclude`. Treat their behavior as local candidate implementation,
not committed baseline. The current task-scoped index adds the listed
repository-history tools; this status note describes their prior provenance.

These files are candidate additions under the user-authorized tracking task.
The two `evolution_worker.py` / `evolution_evaluator.py` files are already
tracked but implement the separate skill-evolution queue and are out of scope
for the repository-history taxonomy bundle.

- `tools/infra/evolution_extract.py` streams commit metadata and changed-path
  / numstat records.
- `tools/infra/evolution_taxonomy.py` assigns multi-label weak commit-change
  categories from message and path regexes (`weak-rule-v2`). The confidence
  values are rule weights, not calibrated probabilities.
- `tools/infra/evolution_path_habitat.py` summarizes changed-path habitats.
- `tools/infra/evolution_ingest.py` ingests those streams into `evo_*`
  collections. `tools/infra/darwin_phylogeny_pipeline.py` orchestrates
  extraction, labels, rendering, optional ingest, and optional tree export.
- `tools/infra/darwin_phylogeny_dashboard.py` builds a separate recent-history
  dashboard and marks module-level joins as cohabitation unless exact evidence
  is explicitly supplied.

### Existing non-evolution codebase classification

- `tools/quality/repo_lean_scope_audit.py` classifies tracked Lean files into
  `lake_package`, `forensic_or_fixture`, or `unclassified_nonpackage`. This is
  package/debt scope classification, not mathematical taxonomy.
- `tools/quality/check_python_cpg_gate.py` consumes Python CPG role classes
  (`ACTIVE_CI_CRITICAL`, `ACTIVE_TOOL_LIBRARY`, `ACTIVE_RUNNER_UTILITY`,
  `DOCUMENTED_REFERENCE`, `CPG_ORPHAN_CANDIDATE`). These provide a distinct
  Python tooling-role surface; they do not classify Lean declarations or
  commit ancestry.
- The tracked `tools/infra/python_ast_dag_ingest.py` exports Python AST nodes
  and typed AST/call/import edges. Its run manifest and per-script role report
  are distinct outputs with different coverage; validate their schemas before
  joining them.
- The Darwin weak-label taxonomy and these package/tool-role classifiers are
  complementary facets. There is no single repo-wide classifier that merges
  all artifact kinds, ownership, Lean theorem status, InfoTree structure, and
  commit history into one provenance-preserving schema in the paths audited.
- `tools/infra/darwin_dna_bridge.py` connects the two Arango databases at the
  application level because cross-database AQL is unavailable. It explicitly
  describes module-path links as habitat cohabitation; it lacks historical
  declaration spans/diff-hunk overlap for exact edit claims.
- `tools/infra/darwin_tree_visualizer.py` has explicit direct/declaration join
  modes, field allow-lists, and a labeled resolution status.

## DAG, InfoTree, and Hodge connection

The compiler-backed declaration DAG and raw InfoTree are separate graph
surfaces. `lean/DAG/Indexer.lean` exports declaration dependencies and
versioned expression fingerprints. `lean/DAG/RawInfoTreeExport.lean` exports
InfoTree roots/nodes/edges and constructor-specific payload/context data.
`tools/infra/arango_raw_infotree_ingest.py` writes InfoTree collections;
`materialize_lossless_infotree.py` constructs raw and overlay files. The
export contract calls the current InfoTree export loss-audited rather than
fully lossless: full syntax-object/expression graphs and assignment closure
remain incomplete in documented areas.

`tools/infra/arango_causal_chiral_cone_prompt.py` traverses the authoritative
declaration graph and can enrich cones with InfoTree/SCC data when coverage
exists. `tools/infra/causal_cone_cross_sections.py`,
`causal_cone_spectrum.py`, `graph_hodge_spectrum.py`, and the Lean `DAG`
Hodge owners provide additional causal and topological analyses. These do not
automatically join the offline DNA packet schema to historical InfoTree
records.

The two Arango lanes are configured separately in
`docs/ASTAQLHASH-HOWTO.md`: the AST/InfoTree lane defaults to port 8530 and
database `infogeometry`; the Darwin commit lane is logically separate and
commonly uses database `darwin_commits`. Runtime endpoint/database freshness
and collection contents must be checked before any live-data conclusion.

## Classification model: keep axes independent

“Full classification of the codebase” should be a faceted inventory, not one
single Linnaean label. Recommended independently versioned axes:

1. **Artifact kind:** Lean source, Python/tooling, docs, generated artifact,
   external reference, runtime data; determined from provenance and parsers.
2. **Repository location / habitat:** module, subsystem, package, or tool
   surface; descriptive and path-derived.
3. **Commit change category:** multi-label weak rules, with rule ID and matched
   evidence; never represented as a calibrated probability without validation.
4. **Lean declaration role:** compiler-reported kind, namespace, imports,
   dependency edges, attributes, source ranges.
5. **Proof/elaboration profile:** InfoTree node constructors, syntax/token
   statistics, goal/context surfaces, and explicit coverage/leakage state.
6. **Structural affinity:** algorithm-versioned type/value/de Bruijn markers
   and graph neighborhood features; candidate similarity only.
7. **Formal status:** source declaration, kernel-checked result, assumptions,
   or audit status, derived only from compiler/build evidence and not from a
   taxonomy model.

Each label should carry source commit or snapshot ID, file/range or graph row
key, extractor version, rule/model version, evidence references, and a status
such as `observed`, `weak_rule`, `model_candidate`, or `kernel_checked`.
Never merge these statuses into a single “species confidence.”

## Development plan (reuses existing owners)

1. **Specify the producer contract** for historical DNA snapshots using the
   existing `repo-dna-snapshots/v1` consumer expectations, adding explicit
   snapshot source hash, toolchain/manifest fingerprint, generation ID,
   declaration key/name, native `typeDigest`/`valueDigest`, algorithm versions,
   and InfoTree root/coverage references. A manifest is provenance metadata,
   not independent verification.
2. **Build per-revision captures without shared `.lake` links.** For each
   selected commit, obtain exact source bytes, compile under the pinned
   environment in a safe isolated strategy, and run the native Lean exporters.
   Respect the no-linked-worktree `.lake` rule and single-flight build lock.
   Record failures and partial coverage explicitly; never label failed or
   uncompiled snapshots as DNA.
3. **Add a loss-audited InfoTree join** keyed by `(commit SHA, generation,
   rootKey, nodeKey)` and declaration source range/key. Retain raw rows and
   coverage/leakage; overlays remain additive. No cross-run node-ID joins.
4. **Keep Arango ingest append-only/versioned.** Use generation collections
   and validate before selecting a generation. Do not refresh/truncate live
   `decls`, `edges`, or `raw_infotree_*` as routine analysis.
5. **Extend classification output as facets.** Reuse weak-label and habitat
   producers; add declaration/InfoTree facets from existing compiler exports.
   Calibrate label weights on human-reviewed holdouts before interpreting them
   probabilistically.
6. **Use graph/Hodge/GPU analyses after provenance validation.** Compute
   per-edge-type causal cones and Hodge summaries, then optional GPU embeddings
   or attention over typed feature vectors. Store model version, features,
   and scores as derived annotations; never overwrite observed edges or
   promote similarity to ancestry/equivalence.
7. **Render linked views:** commit ancestry, declaration dependency DAG,
   InfoTree/proof structure, and candidate affinity as distinct togglable
   layers. Clicking any relation must expose its evidence and exact snapshot.

## Audit boundaries

- Source files and tests were inspected; the targeted offline phylogeny tests
  passed. No live Arango query, graph refresh, Lean build, or GPU workload was
  run. The tests do not exercise the Arango bridge/ingest or recent dashboard
  adapters.
- The search covered repo-owned Darwin/evolution tools, repository-evolution
  modules, DAG/InfoTree exporters and ingest, causal-cone/Hodge tools, and
  related tests/docs, plus the Lean package-scope audit and Python CPG role
  gate. It did not classify every file or Lean theorem in the repository.
- Names, weak labels, graph adjacency, fingerprint matches, Hodge summaries,
  and model scores are navigation/classification evidence only. They do not
  establish theorem meaning, equivalence, or proof status.
