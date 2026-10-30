# Repository evolution and declaration DNA

The tools in `tools/repository_evolution/` provide three separate views:

- recorded Git ancestry, including every ordered merge parent;
- structural affinity inferred from observed, comparable DNA markers;
- exact Hodge analysis of an unfilled graph 1-complex.

The HTML viewers work offline. Git and fingerprint provenance remain explicit:
an inferred affinity edge is not a recorded parent, and a fingerprint match is
not a Lean equivalence proof. See
[the mathematical contract](REPOSITORY_EVOLUTION_MATHEMATICAL_CONTRACT.md)
for the definitions, alignment assumptions, source audit and scope.

## Generate the ancestry explorer

Run from the repository root with Python 3.10+ and Git:

```bash
python3 tools/repository_evolution/phylogeny_export.py \
  --repo . \
  --since 2025-10-27T00:00:00Z \
  --until 2026-10-28T00:00:00Z \
  --repository-url https://github.com/nickgou-nuke/info-geometry-lean \
  --out artifacts/repository-evolution/phylogeny.json

python3 tools/repository_evolution/render_explorer.py \
  --data artifacts/repository-evolution/phylogeny.json \
  --out artifacts/repository-evolution/repository-phylogeny.html
```

Open `artifacts/repository-evolution/repository-phylogeny.html`. The renderer also
copies the authored `dna-affinity-viewer.html` beside it, so the companion link
works in a newly generated output directory. It escapes embedded JSON and
refuses to overwrite source inputs, templates or the companion viewer.

Choose the desired date interval; the example covers 27 October 2025 through
27 October 2026, with an exclusive upper boundary. The exporter reads current
local branches (`refs/heads/*`), all remote-tracking branches
(`refs/remotes/*`), and commit-valued tags without fetching or modifying the
checkout. This includes locally retained archive and review refs when present;
inspect the output's `source.refs` and `ref_scope` to see exactly which tips
contributed. Update the desired refs separately before exporting.

It collects reachable history before filtering by committer time. A skewed
timestamp therefore cannot prune an ancestor traversal. Outside-window parents
and shallow-history boundaries are explicit. Deleted/unreachable histories are
outside the export. Git object identifiers currently use SHA-1.

The viewer searches every exported commit and inserts a selected collapsed
revision into the drawing. It offers topological order or stored time,
pan/zoom, full-graph ancestor/descendant cones, and native declaration inspection.
Cone counts exclude the seed and remain independent of display compression.

Only unbranched interior revisions are collapsed. Every retained link stores
its full hidden chain; the exporter checks that expanding the drawing recovers
the complete ordered parent-edge multiset. Horizontal position is a layout
choice, and topological vertical spacing is not elapsed time.

## Optional exact Hodge report

The exporter, renderer and DNA inference use the standard library. Hodge
analysis additionally uses NumPy and SciPy. A tested optional environment is
pinned separately and requires Python 3.11+:

```bash
python3 -m venv .venv-repository-evolution
.venv-repository-evolution/bin/python -m pip install \
  -r tools/repository_evolution/requirements-hodge.txt

.venv-repository-evolution/bin/python \
  tools/repository_evolution/ancestry_hodge.py \
  --input artifacts/repository-evolution/phylogeny.json \
  --out artifacts/repository-evolution/ancestry-hodge.json \
  --witness-out artifacts/repository-evolution/ancestry-hodge-cycles.json

.venv-repository-evolution/bin/python \
  tools/repository_evolution/render_explorer.py \
  --data artifacts/repository-evolution/phylogeny.json \
  --hodge artifacts/repository-evolution/ancestry-hodge.json \
  --out artifacts/repository-evolution/repository-phylogeny.html
```

The renderer checks the report's input-file SHA-256 and successful-check status
before embedding it. A report for another export is rejected.

The analysis uses the full `commits` array, never the display-compressed graph.
It constructs the actual sparse incidence B, D=[[0,B],[Bᵀ,0]], and
Γ=diag(+I_vertices,−I_edges). Integer checks cover chirality, D², rank witnesses
and an independent signed cycle basis. The report specifies coefficient field,
boundary policy, root/tip scope and the absence of filled 2-cells. It does not
run an eigensolver or compile Lean.

## Infer a DNA affinity tree without historical SHAs

```bash
python3 tools/repository_evolution/dna_character_tree.py \
  --input /path/to/observed_profiles.json \
  --out artifacts/repository-evolution/affinity.json
```

Open the generated companion viewer, or open
`tools/repository_evolution/dna-affinity-viewer.html` directly, and import
`affinity.json`. It starts without preloaded data.

The generic `repo-character-profiles/v1` schema identifies each taxon and its
categorical markers. The native `repo-dna-snapshots/v1` adapter uses actual
declaration `typeDigest`/`valueDigest` objects, exact qualified names, version
agreement and a closed-term gate. A generation ID is sufficient; historical
commit binding is unnecessary for inference.

The engine supports 3–128 taxa. It excludes incomplete/incompatible marker
columns for every pair, refuses an empty comparable panel, and computes
equal-weight categorical mismatch. Neighbor joining uses exact rational
arithmetic and deterministic ties. Negative lengths are retained. Pairwise
tree-fit residuals and exact/sampled four-point diagnostics quantify lost fit.

The output is an **unrooted structural-affinity tree**. Internal nodes are
inferred groupings, not identified ancestors. The viewer's equal-angle display
is explicitly not to scale; selecting an edge reveals its exact signed length.
Zero-length edges and tie breaking do not imply support for a split.

Marker homology remains an input assumption. Hash bit distance is never used,
and correlated type/proof/subterm features are not independent mutations.
No molecular clock, bootstrap confidence or Lean equivalence claim is made.

## Attach observed fingerprints to Git revisions

Historical attachment is a separate operation from affinity inference.
Use `--dna snapshots.json` when exporting, or the ancestry viewer's file input.

```json
{
  "schema": "repo-dna-snapshots/v1",
  "repository": "https://github.com/nickgou-nuke/info-geometry-lean",
  "snapshots": [{
    "commit": "FULL_40_CHARACTER_COMMIT_SHA",
    "generation": "ACTUAL_IMMUTABLE_GENERATION",
    "provenance": {
      "binding": "source-verified",
      "source_commit": "THE_SAME_FULL_COMMIT_SHA",
      "working_tree_clean": true,
      "build_fingerprint": "RECORDED_BUILD_FINGERPRINT",
      "toolchain": "RECORDED_TOOLCHAIN"
    },
    "declarations": []
  }]
}
```

This is a contract illustration, not measured data. Replace placeholders and
`declarations` with actual producer records. Do not infer an old generation's
source from today's HEAD. Use `source-verified` only when producer records
establish that binding. The viewer labels it **manifest-attested** because it
validates the packet but does not independently verify the build/source claim.

Preserve native nested fields:

```text
name, key, module, relFile, range, kind
typeDigest / valueDigest:
    algorithmVersion, digest, nodeCount, openTerm
typeFingerprint / valueFingerprint / shapeHash:
    algorithmVersion, shapeHash, nodeCount, constructor counts, ...
canonicalTypeHash, canonicalValueHash, dagShapeHash
```

UInt64 values remain decimal strings, matching Lean JSON. Metadata proxies
are rejected. The historical viewer compares exact declaration names and
closed, equally versioned type/value digests. A rename appears as removal and
addition; absent, open or incompatible values remain incomparable.

The existing `tools/leantrail/arango_dump.py` can export the user's selected
declaration and edge collections as nodes/links. Use the actual deployment
configuration and immutable-generation collection names; this new package
does not discover or connect to an Arango instance itself.

## Source layout and validation

Implementations and authored HTML assets live in `tools/repository_evolution/`.
Focused suites live in `tests/` and run from the repository root:

```bash
python3 -m unittest discover -s tests -p test_repository_phylogeny_export.py -v
python3 -m unittest discover -s tests -p test_repository_dna_character_tree.py -v
python3 -m unittest discover -s tests -p test_repository_ancestry_hodge.py -v
python3 -m unittest discover -s tests -p test_repository_evolution_render.py -v
```

Run them sequentially. The Hodge suite explicitly skips when its optional
dependencies are absent; the dedicated Repository evolution CI job installs
the pinned environment and runs all four suites. Other suites need only Git
and the standard library.

Tests cover real temporary Git histories, nonmonotone timestamps, boundary
parents, shallow clones, octopus merges, tag reachability, fingerprint contracts,
categorical NJ, missing data, signed cycles, disconnected carriers, exact rank
witnesses, renderer source binding and offline companion assets.

Generated exports, embedded ancestry HTML, reports, witnesses and screenshots
belong under ignored `artifacts/` or `reports/`. They are not source fixtures
and are not committed. The mathematical contract records one dated capture;
regeneration uses the refs available at the time of the new run.
