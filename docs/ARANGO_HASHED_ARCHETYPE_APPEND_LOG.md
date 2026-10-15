# Append-only hash and archetype graph

This design layers onto the existing ExprArango and wire-topology formats. Lean
source and the kernel remain authoritative. The Arango hashes support exact
lookup, structural deduplication, and graph navigation; they do not establish
proof equivalence.

## Identity layers

A Pantograph session records two environment labels. `buildFingerprint` links
to an existing graph generation and is caller-supplied when that generation is
used. `environmentFingerprint` is computed locally from the repository
toolchain and Lake manifest, the captured source, the `.olean` dependency list
reported by Lean, and the Pantograph Git/source/executable inputs. Each request
adds an intent event, and its response adds a child event. The event key is a
SHA-256 of canonical JSON identity data, including the parent event key. Thus
identical actions from the same parent and environment deduplicate, while the
same action from different parents remains a distinct point in the walk tree.
Optional `--decl-fingerprint` and paired `--scc-generation` /
`--scc-fingerprint` fields are also included in every root, request, and
response event identity. The SCC label is generation-local: the same SCC
fingerprint in another generation is a distinct location unless a separate
archetype-signature lookup connects them. These labels improve localization;
they do not prove path equivalence.

Instead of supplying those labels manually, `--archetype-generation-id ID
--decl-name NAME` resolves them from a complete `ig_graph_generations/ID`
manifest. The session build fingerprint must equal the manifest fingerprint.
A declaration can occur in many expression SCCs, so lookup retains the sorted
complete SCC/archetype occurrence set. `sccFingerprint` is the SHA-256 of this
generation-local cover; the individual `(sccKey, sccPatternHash, signatureKey)`
rows are stored once in `pantograph_scc_covers`; revision events reference the
immutable cover document by `sccCoverKey`. The resolver drains every Arango
cursor batch before computing the cover, so the fingerprint cannot silently
represent only the first default-sized page. It never chooses an arbitrary
SCC. The declaration fingerprint is derived from that generation's stored
`patternHash` and `roleHash`, and is explicitly a retrieval label.

`pantograph_requests` and `pantograph_responses` retain the raw protocol lines.
`pantograph_revision_events` plus `pantograph_revision_edges` represent the
content-addressed execution walk. `pantograph_event_occurrences` points from
each session-local request/response record to the shared event. Session-local
Pantograph state IDs remain aliases, never persistent proof-state identities.

### Pantograph InfoTree tactic projection

Pantograph's `frontend.process` collects substantive `TacticInfo` nodes from
the compilation-step InfoTrees when the request supplies `invocations` as an
output path. (The Lean structure uses `invocations?` internally, while its
derived JSON field is `invocations`.) The stream wrapper reads that JSON after forwarding the compiler
response. It stores normalized `(goalBefore, tactic, goalAfter, usedConstants)`
records once in `pantograph_frontend_fragments`, keyed by SHA-256 of canonical
JSON. `pantograph_frontend_fragment_occurrences` connects each response event
to those shared records and retains the compilation-unit source boundary,
session, sequence, unit, and invocation index.

This is Pantograph's tactic-invocation projection, not a lossless InfoTree
export and not a Lean proof identity. Source locations and constant ordering do
not affect the reusable fragment key; the exact goal/tactic text and used
constant set do. Reuse is therefore conditional on an exact normalized match.
The repository's `RawInfoTreeExport.lean` plus
`arango_raw_infotree_ingest.py` remains the separate fuller compiler-memory
export path.

### Exact raw InfoTree generation links

`batch_raw_infotree_export.py` captures per-source provenance around each
validated export: project-relative `sourcePath`, SHA-256 of the exact source
bytes, and a computed `leanContextFingerprint`. The context manifest covers
`lean-toolchain`, `lakefile.lean`, `lake-manifest.json`, Lean/Lake versions,
the source import closure's `.olean` bytes, and the target module `.olean`.
The per-file provenance is copied into merged `source_metadata`, then into the
immutable `raw_infotree_generations/<id>` manifest at ingest. Synthetic runs
with `--allow-missing-olean` deliberately do not claim this provenance.

The Pantograph stream computes the same source-context fingerprint separately
from its wider environment fingerprint (which additionally includes
Pantograph's own source and executable). To link an export, pass
`--raw-infotree-generation-id <id>` together with `--source-snapshot`. The
stream requires a complete generation and an exact match on project-relative
source path, source-byte SHA-256, and `leanContextFingerprint`, then appends an
immutable edge in `pantograph_raw_infotree_generation_links` from the session's
root revision event to the raw generation manifest. Caller-provided
`buildFingerprint` is not used as proof of this match. Old generations without
captured provenance remain unlinked; they are not retroactively blessed by
hashing the current source file.

The link can be inspected with:

```aql
FOR link IN pantograph_raw_infotree_generation_links
  FILTER link.sessionId == @sessionId
  LET event = DOCUMENT(link._from)
  LET generation = DOCUMENT(link._to)
  RETURN {
    eventKey: event._key,
    generationKey: generation._key,
    sourcePath: link.sourcePath,
    sourceSha256: link.sourceSha256,
    leanContextFingerprint: link.leanContextFingerprint
  }
```

Example request:

```json
{"cmd":"frontend.process","payload":{"file":"...","readHeader":false,"inheritEnv":false,"invocations":"tmp/invocations.json","newConstants":false}}
```

The output file is read only after Pantograph responds. If it is absent or its
unit/count data disagrees with the response, the session records a
`frontend_invocations_capture_failed` event and continues forwarding protocol
traffic; it does not claim that the projection was stored.

The `--source-snapshot` option stores exact source text in
`pantograph_source_snapshots`, keyed by its SHA-256. With a snapshot, the stream
computes and stores `environmentManifest` and its fingerprint. The manifest
hashes `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`, and uses
`lake env lean --deps` on the captured source and each startup module to
enumerate imported `.olean` files; this is a dependency query and does not
build them. It hashes those artifacts, the Pantograph working tree and REPL
binary. Pantograph still runs the recorded command against its loaded Lean
environment. Without a source snapshot, no independent environment manifest
is produced and the session is marked request-log-only.

Example (run from the repository root after building the external Pantograph
checkout for the pinned toolchain):

```bash
python3 tools/infra/pantograph_arango_stream.py \\
  --session-id run-2026-10-06-a \\
  --build-fingerprint "$BUILD_FINGERPRINT" \\
  --archetype-generation-id "$GRAPH_GENERATION_ID" \\
  --decl-name InfoGeometry.External.Virasoro.FockSpaceSugawara.energy_bound \\
  --source-snapshot lean/InfoGeometry/External/Virasoro/FockSpaceSugawara.lean \\
  -- external_refs/Pantograph/.lake/build/bin/repl InfoGeometry.All
```

To continue a saved event-tree branch, also pass
`--parent-event-id <pantograph_revision_events document key>`. The wrapper
logs each input request before forwarding it and records the returned response
before accepting the next request.

## Read-only replay check

`pantograph_arango_replay.py` fetches a session's snapshot and ordered request /
response records, checks the snapshot digest, compares the current source file
with the captured text, recomputes the environment manifest (including current
`.olean` bytes and Pantograph source/executable), and refuses a mismatch. It
then starts a fresh Pantograph process using the recorded command, remaps
process-local state IDs, and compares goals, diagnostics, and other response
content. It performs no Arango writes.

```bash
python3 tools/infra/pantograph_arango_replay.py \\
  --session-id run-2026-10-06-a \\
  --database pantograph_stream_test
```

A `matched` result means the request log reproduced the recorded protocol
responses with the same locally fingerprinted inputs and matching source
snapshot; it is not a new Lean proof or a proof that different sessions are
equivalent. The graph-generation `buildFingerprint` remains a separate caller
label when linking to a preexisting generation.

## Hash bundle and coarse archetypes

The existing `wire_topology_transform.py` already produces `sccPatternHash`,
`patternHash`, `roleHash`, and the finer Expr/De Bruijn hash fields. Immutable
ingest mode in `arango_wire_topology_ingest.py --build-fingerprint ...` uses
those existing outputs. It hashes the generation fingerprint from the exact
JSONL bytes and declared environment fingerprint, then writes generation-local
collections such as `ig_scc_g_<id>`.

For each SCC it derives a canonical bundle containing its `sccPatternHash` and
the sorted `(hash kind, declaration hash)` pairs for its member declarations.
A SHA-256 of that bundle keys `ig_archetype_signatures`; this is the cross-run
deduplication index. `ig_archetype_occurrences` links each generation-local SCC
to the shared signature. The signature is an archetype candidate for retrieval,
not a theorem that two SCCs are isomorphic or mathematically equivalent. Its
scheme version and exact bundle are stored to make collisions or normalization
changes detectable.

Each completed import publishes one immutable document in
`ig_graph_generations`. A failed ingest leaves no `status: complete` record; the
partial generation collections are not reused or overwritten. Generate a new
export/fingerprint for a retry. No previous generation is truncated.

## Useful AQL lookups

Find all generation-local SCC instances with a matching signature:

```aql
LET signature = DOCUMENT(CONCAT("ig_archetype_signatures/", @signatureKey))
FILTER signature != null
FOR occurrence IN ig_archetype_occurrences
  FILTER occurrence._to == signature._id
  LET scc = DOCUMENT(occurrence._from)
  RETURN {
    generationId: occurrence.generationId,
    scc: scc,
    hashBundle: signature.hashBundle
  }
```

Find current leaf events in one source/environment lineage:

```aql
FOR event IN pantograph_revision_events
  FILTER event.sourceSnapshotSha256 == @sourceSnapshotSha256
  FILTER event.buildFingerprint == @buildFingerprint
  FILTER LENGTH(
    FOR edge IN pantograph_revision_edges
      FILTER edge._from == event._id
      LIMIT 1
      RETURN 1
  ) == 0
  RETURN event
```

A hash match can identify a candidate SCC or expression structure. To establish
that two paths are directed-homotopic, define the allowed local path rewrites
and provide witnesses for them; matching a terminal hash alone is insufficient.
