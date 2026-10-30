# Darwin phylogeny and codebase taxonomy audit

**Status:** source audit, implemented scanner, and implementation plan
**Scope:** tracked Git/commit evolution, declaration-DNA, InfoTree, graph/Hodge,
and classification tooling, plus identified ignored worktree candidates,
inspected on 2026-10-28. This is not a claim that all mathematical owner
declarations or all Arango runtime rows were audited.

## Implementation delta — 2026-10-30

### Committed sample capture completed; expansion bottleneck measured

IdempotentCartan capture completed successfully after **967.79 seconds**.
Both queued suites then passed: **11 fossil-ingest tests** and **16 batch-export
tests**. The stop request is no longer operationally needed; no stop was sent.
Raw topology validates, but capture remains partial: 36 roots, 12,231 nodes,
12,195 tree edges, and 40,888 leakage records. Raw storage occupies **444 MB**.

The maintained DNA extractor accepted one source with 110 feature rows and
zero rejected captures. Its fossil overlay links 12,231 nodes and records two
path events, 22 line spans, 234 committed-origin lines, and 50 uncommitted
lines. The generation receipt at
`/tmp/darwin-idempotent-cartan-generation-v4.json` has digest
`e5b2bcfa47e0c4bccbcb807b9fbf5ec55cb5da8ef34b642ffd3b4e7b0a3c1ad2`.
Complete coverage is restricted to this one selected module. Referenced
declaration-link rows are not a count of theorems defined in that module.

Arango dry-run preflight at
`/tmp/darwin-idempotent-cartan-arango-preflight-v4.json` exposes the scaling
bottleneck: 516,555 local-context reference documents generate **2,997,837
reference-to-declaration edges**, and 5,660 metavariable-context references
generate **508,990 context-reference-to-declaration edges**. Those are repeated
expansions of shared contexts, not millions of distinct mathematical relations.
This large raw generation has **not** been ingested. The next storage refactor
must represent shared context membership once and preserve per-node references,
with explicit schema/query migration and equivalence checks, before a
repository-wide capture/ingest campaign. Existing CFSGPort live generations
remain unchanged.

### Full inventory refresh after database integration

The existing scanner completed a new full repository inventory at
`/tmp/darwin-full-current-map-post-integration.json.gz`: **42,122 artifacts,
25,951 Lean sources, 246,954 lexical declaration candidates, and 91,687 local
Lean import edges**. The Python oracle analyzed 2,913 repo-owned scripts and
2,655 reference files; the map retained 1,337 Python-import and 252 test-import
edges after scope filtering.

This is **not a stable whole-repository generation**:
`lean/InfoGeometry/Exceptional/CFSGPort/ChevalleyRootOperatorMirror.lean`
changed during scanning. Compiler source hashing also detected concurrent
changes, so zero compiler-fingerprint summaries were joined. No training or
semantic classification result is inferred from this mixed-generation map.

The three unindexed Lean source paths remain `lean/AuditNative.lean`,
`lean/AuditStrict.lean`, and `lean/KaplanskyCliffordBridge.lean`. The latter
imports `Mathlib.LinearAlgebra.Finrank`, which the scanner could not resolve
in local/cached dependency source. The other 46 unresolved imports belong to
sandbox/historical candidates. These are scanner findings requiring source
and build investigation, not proof failures established by this scan.

### Capture resource observation

Read-only host process inspection during IdempotentCartan capture found the
exporter's Lean child actively consuming approximately one CPU core, with
5,597,240 KiB resident memory after about 12 minutes. This is active computation,
not evidence of a dead process or a completed capture. The current source hash
still matches the scoped scan:
`460c5eafe4d6496a2276f7788a2fccfb8aa5c9bbd4839cf45f5571abfb66c16f`.
Another Lean process was also visible; this agent did not launch another build
or stop either process. Both regression suites remain queued under the shared
lock. Permission to stop capture 40947 was requested but has not been received.

Source inspection shows that the batch path executes `lake env lean --run`
and that term digests already memoize structural expression nodes within each
digest call. Replacing that memoization with a new duplicate implementation
is unwarranted. Cross-call hashing costs, context traversal costs, and native
execution remain candidates for profiling; this process snapshot does not
identify which dominates. No exporter source or fingerprint contract was
changed during the active capture.

### Primary-literature check for remaining model work

Primary-source abstracts were read through browser-harness on 2026-10-30:

- Guo et al., *GraphCodeBERT: Pre-training Code Representations with Data
  Flow*, ICLR 2021, https://arxiv.org/abs/2009.08366. The paper uses data-flow
  structure, edge prediction, and code/structure alignment alongside masked
  language modelling. Transfer candidate: compare source-only, typed-graph,
  and combined views using the existing feature and baseline owners. Lean
  declaration references and InfoTree context edges must retain their own
  semantics; they are not automatically data-flow edges. The abstract's
  downstream results do not validate this repository's taxonomy.
- Angelopoulos and Bates, *A Gentle Introduction to Conformal Prediction and
  Distribution-Free Uncertainty Quantification*,
  https://arxiv.org/abs/2107.07511. This identifies conformal prediction as a
  candidate uncertainty-set framework. Only the abstract was inspected in this
  check; no theorem assumptions or guarantee for dependent codebase samples
  were verified. A method-specific full-text audit and separate reviewed
  calibration/evaluation data are required before claiming coverage here.

Source tracing confirms that `latent_taxonomy.py` exposes uncalibrated sigmoid
scores and fixed abstention thresholds, while `train_taxonomy_baseline.py`
reports uncalibrated Brier scores. These are existing baseline diagnostics,
not conformal guarantees. Priority remains collecting valid reviewed labels
and evaluating the existing structural/source ablations before adding a new
attention architecture or claiming that literature methods are optimal here.

### Per-capture live exporter diagnostics

The batch wrapper previously captured exporter stderr in memory until exit,
so phase messages were invisible while a slow capture ran. Future captures
now stream stderr to `export.stderr.log` inside their newly created capture
directory. The final report reads at most the last 32,000 bytes and retains
an 8,000-character diagnostic tail. Timeout reports preserve that log without
granting capture provenance. The file is diagnostic evidence, not a raw-row
bundle member or a DNA feature.

A regression test verifies that the log is readable during execution, survives
a simulated timeout, and produces a bounded report tail. Its suite is queued
under the shared lock (session 39429), behind capture 40947 and the fossil-reuse
suite 70975. No test result is claimed yet. The active capture predates this
wrapper change and therefore does not gain a live log retroactively. Lean
exporter source was deliberately left unchanged during that capture.

### Rename-aware exact fossil reuse

The live reuse matcher previously checked commit, destination path, change
type, and endpoint existence, but not the rename source. It now also compares
`old_path` with the captured `oldPath`. Base64-only source paths conservatively
fall back to the captured event rather than claiming an unverified text match.
Conflicting old paths sharing one base edge key disable reuse for that key,
including when the candidates arrive in different batches. Both captured
events remain available as fallback records.

Regression cases for within-batch and cross-batch conflicts are staged; their
execution is queued behind the active InfoTree capture (test session 70975).
No passing test result is claimed yet. Independently, a read-only live call to
the revised matcher on the committed IdempotentCartan events returned **two
exact reused edges, zero fallback events, and sampled HEAD present**. Receipt:
`/tmp/darwin-idempotent-cartan-reuse-preflight.json`. This checks actual existing
Git event edges, not a completed raw-InfoTree overlay generation. Capture
session 40947 remains live, so the full source-to-fossil join is still pending.

### Committed noncommutative dependency integration scope

The next integration target is `InfoGeometry.Core.IdempotentCartan`, a
committed noncommutative Peirce-parity dependency of `YangMillsOrbitGramian`.
The fresh selected-source map
`/tmp/darwin-idempotent-cartan-map-v4.json.gz` reports a stable selected source
and Git revision, 30 lexical declaration candidates, one local dependency
crossing the inventory boundary, and one external import. Its stale global
compiler fingerprint index remains explicitly unjoined.

The scoped fossil extractor and the independent `evolution_extract`
file-status stream agree exactly on two `(commit, change type, path)` events:
the addition and subsequent modification of this module. Those two file-event
rows were passed to `evolution_ingest --preserve-existing --database
infogeometry`, retaining existing documents. Source artifacts are
`/tmp/darwin-idempotent-cartan-fossils-v4.jsonl` and
`/tmp/darwin-idempotent-cartan-status-v4.jsonl`.

Current-source raw capture is running in session 40947 at
`/tmp/darwin-idempotent-cartan-v4`; the live handle was polled successfully.
Until it finishes and passes validation, no DNA extraction, fossil overlay,
or exact-reuse receipt is claimed for this sample. This scope exercises real
committed history; it does not substitute for the parent Yang–Mills owner or
whole-repository coverage.

### Reviewed-label readiness inspection

The saved materialization report
`/tmp/darwin-taxonomy-adjudication-empty-manifest.json` contains 480 pending
decisions and **zero accepted human-adjudicated annotations**. This is evidence
about that packet, not a repository-wide assertion that no labels exist.
Pending review tasks are not a training corpus and cannot support a claim of
validated semantic classification.

The readiness gate previously applied `set()` to labels before validating
their element types. Nested JSON arrays/objects could therefore crash the
audit. It now rejects malformed and duplicate labels before coverage counting,
reports `malformedRowIndices`, and leaves readiness false. Duplicate labels
are rejected rather than silently normalized into an asserted reviewed set.
The readiness and baseline-training suites passed **28 tests** in Sage under
the shared lock, including seven malformed-label cases with recomputed input
digests to isolate semantic validation from checksum validation.

### Live habitat missingness readback and label join

The previously pending live habitat query completed: 449 habitats, eight with
entirely unknown churn, 33,262 unknown-churn habitat associations, and 32,965
observed-churn associations. These are association counts, not distinct commit
counts, and reflect the database when that query executed.

The habitat query's correlated label subquery has been replaced with a
primary-key lookup, matching the importer contract `evo_labels._key = sha`.
The bridge aggregation and preservation suites passed four tests. The separate
read-only compatibility check completed: **13,682 label rows, zero mismatched
keys**. The new live query returned the same four aggregate figures above.
This verifies key compatibility and aggregate agreement on this database,
not a controlled timing comparison or full output-by-output comparison.
Both query sessions are terminal. Other databases with legacy labels must
honor the same key contract before using the primary-key join.

### Churn missingness propagated to bridge and visualizer

The tree visualizer now emits null churn with `churn_status=unknown` for
uncollected or absent statistics and displays it as `unknown`. Observed zero
remains zero. Both DNA-bridge AQL projections preserve unknown churn; the
coarse habitat share estimate remains null when its commit churn is unknown.
Habitat summaries expose `observed_churn_commits` and `unknown_churn_commits`,
sum only observed values, and return null for an entirely unobserved total.
These are habitat associations, not declaration-local mutation measurements.

The visualizer, bridge-aggregation, and evolutionary-query suites passed
**11 tests** in Sage under the shared lock. The bridge test covers mixed,
entirely unknown, and observed-zero habitats. A read-only live habitat query
was launched for AQL verification; its outcome remains pending at this entry.

### Missing diff statistics in evolutionary query consumers

`evolutionary_queries.load_commit_data` previously converted null insertion
and deletion counts to zero and unknown file counts to one. It now preserves
unknown churn, including explicit `diff_stats_status=not_collected`. The
per-changed-file ratio returns unknown for missing data or a zero denominator.
Peak-ratio rankings exclude and count those associations. Cohabitation summaries
retain all associations, sum only observed churn, and report the unknown count;
an entirely unobserved sum is null rather than zero.

Nine focused Sage tests passed under the shared lock. A live read-only query
of `darwin_commits` returned 13,986 rows: 13,983 with unknown churn and two with
observed zero churn. The additional existing database rows were preserved by
the refresh. Separate churn projections in `darwin_tree_visualizer.py` and
`darwin_dna_bridge.py` still require a missingness audit; this change does not
claim that every downstream consumer has been repaired.

The older shortstat extraction subsequently completed successfully with
13,983 commits. Its complete output remains separate and has not been imported;
session 81722 is terminal, so no metadata-extraction process remains pending.

### Metadata-only fossil refresh and live coverage check

The extractor's previous commit stream always requested `git log --shortstat`,
which computes historical diffs even when only commit metadata is needed.
`evolution_extract --metadata-only` now omits that option, preserves message
text that resembles a shortstat line, and emits null change counts with
`diff_stats_status=not_collected`. Checkpoints bind the extraction mode and
reject a resume under a different mode; old checkpoints retain the default
shortstat interpretation. No source checkout or reconstruction is involved.

The fresh metadata-only stream at
`/tmp/darwin-commit-metadata-only-20261030.jsonl` contains **13,983 unique
commits and 14,339 parent edges**. Every commit and ordered parent list matched
`git rev-list --parents --all`. Four Sage regression tests passed under the
shared lock for metadata-only parsing/resume and preservation on ingest.

The existing importer defaults to database `darwin_commits`; the InfoTree
overlay reads the separate `infogeometry` database. Both were refreshed using
`--preserve-existing`, without replacing documents. Independent AQL checks in
both databases found **zero missing expected commits, zero missing or
endpoint-mismatched expected parent edges, and the current HEAD present**.
Readback: `/tmp/darwin-metadata-refresh-readback.json`. These checks concern the
current all-refs export, not removal of additional historical database rows.
They close the missing-HEAD gap recorded by the earlier immutable overlay
receipt; that receipt remains an accurate record of its earlier observation.
Commit-file event refresh and real-event overlay reuse are still pending.

The older shortstat extraction remains a separate live process (session
81722 at last observation), with its own partial/checkpoint files. Its partial
output has not been imported or treated as complete.

### Non-overwriting Git metadata refresh mode

Inspection of `evolution_ingest.py` found that its default duplicate policy is
replacement, which can erase additional fields on an existing document.
The importer now offers `--preserve-existing`: Arango bulk imports use
`on_duplicate="ignore"` for all six evolution collections while adding missing
keys. Existing conflicts are deliberately retained, not reconciled silently.
The mode cannot be combined with `--replace`; invalid batch sizes and the
conflicting modes fail before collection mutation. CLI counts explicitly mean
input rows attempted, not newly created documents.

Regression tests cover annotation/conflicting-field preservation in all six
collections, addition of new commit/parent-edge keys, and rejection before
mutation. Verification is queued behind the shared build lock; no passing
result is claimed yet. The current metadata-only extraction uses the existing
`evolution_extract` tool and writes
`/tmp/darwin-current-commit-metadata-20261030.jsonl`. It has not yet been
imported. Local `git rev-list --all --count` reports 13,983 commits; final
extractor scope/count comparison remains pending. No historical checkout or
repository clone is used.

### Live Arango pipeline verification

The existing ingesters successfully imported the fresh CFSGPort
`MatrixInverseTranspose.lean` capture into **real ArangoDB 3.12.10-1** at
`http://127.0.0.1:8530`, database `infogeometry`, using immutable generation
collections. No existing generation was replaced or truncated.

- Raw generation: `e05e4a108bcdf1d692338b63`, with successful import accounting
  and matching live collection counts. Local receipt:
  `/tmp/darwin-cfsg-arango-live-v4.json`.
- Fossil stage generation:
  `33b83bba7eeff18bec2676500426e9ba7c3d3082960a9368c1c0a60e4fb325ad`, stored in
  `repo_phylogeny_generation_receipts`, status `staged_validated`.
- Live overlay counts: 566 node-to-path links, 357 node-to-line links,
  510 declaration-link-to-line edges, one path fossil, one uncommitted line
  span, zero historical events, and zero dangling endpoints.
- An independent AQL readback dereferenced both endpoints of all 566
  node-to-path edges: all resolved to the selected source with **zero missing
  endpoints**. Readback and persisted receipt were saved at
  `/tmp/darwin-cfsg-arango-readback-v4.json`.

This closes the earlier live-ingestion verification gap **for this one
generation only**. It does not claim full CFSGPort or repository coverage,
lossless capture (1,894 leakage rows remain), or a validated taxonomy.
The evolution base collections exist, but this sampled Git HEAD was absent
from the base commit collection (`snapshotHeadPresentInArango=false`). No
commit relation was fabricated: this staged source has no historical path
events, and all 45 lines are explicitly uncommitted. A sample with real Git
events is still needed to verify exact historical-edge reuse end to end.

### Affinity-tree profile resolution

The existing categorical-distance owner `dna_character_tree.py` already
excludes incomplete marker columns and incompatible algorithm versions rather
than treating missing values as mutations. The output now also reports
`diagnostics.profile_resolution`: distinct retained profiles, constant and
variable marker counts, and groups of taxa indistinguishable on the retained
panel. This matters when filtering removes the only discriminating markers:
deterministic neighbor-joining tie-breaking can still render a resolved tree
even when all observed distances are zero. The report explicitly disclaims
evidence for those distinctions. Observation IDs remain separate; equality of
observed profiles is not semantic equivalence or Git identity. Distinct
profiles likewise do not imply a uniquely supported topology. This additive
diagnostic does not change distances or the inferred tree.
The Sage character-tree and Git phylogeny suites passed **30 tests and seven
subtests** under the shared lock, including missing-column-induced identity
and duplicate native digest profiles with distinct observation IDs.

### Exact topology-feature aggregation at repository scale

`latent_taxonomy._features_for_map` previously enumerated every length-two
walk, with quadratic work at high-degree hubs. It now aggregates second-edge
multiplicities by direction and edge type at each intermediate vertex.
Endpoint identity was never part of this feature, so the feature values and
version remain unchanged. Parallel edges, self-loops, backtracking, and
out-of-inventory boundaries retain their previous semantics. Complexity is
O(E + sum over edges of the number of distinct direction/type pairs at their
intermediate vertex), rather than enumerating all endpoint pairs.

The Sage latent-taxonomy and baseline-training suites passed **30 tests**
under the shared lock. New regression cases compare against explicit walk
enumeration and exercise a 10,000-leaf hub (100 million leaf-to-leaf walks
represented by aggregated counts).

Feature extraction over the saved full inventory
`/tmp/darwin-current-full-20261030-recheck.json.gz` completed in **0.795 seconds**:
42,083 artifacts, 129,069 dependency edges, and 121,772 nonzero walk-feature
entries. This is a single local timing, not a comparative benchmark. The
saved inventory is mixed-generation; this execution is performance evidence
only and does not authorize model training or current taxonomy claims.

### Fresh CFSGPort v4 integration verification

After the authorized Yang–Mills diagnostic stop and locked exporter checks,
the fresh `MatrixInverseTranspose.lean` batch capture completed in 19.4 seconds.
Its report at `/tmp/darwin-cfsg-inverse-transpose-v4/batch_report.json` records
9 roots, 566 nodes, 557 edges, valid topology, and 1,894 projection-leakage rows.
It is explicitly **not lossless**. Source, Lean context, exporter source, and
raw-bundle receipts are present.

The standalone DNA CLI initially failed to import `tools.build_lock`. Its
script entrypoint now adds the repository root to the import path. An isolated
Python subprocess regression checks repository imports from outside the repo.
The Sage DNA, fossil-overlay, generation-manifest, and batch-export suites
passed **71 tests** under the shared lock.

The repaired CLI produced one accepted partial capture with 92 feature rows;
the fossil overlay produced 566 node links. This newly staged module has no
Git path events: all 45 lines are attributed as uncommitted, not fabricated
historical DNA. Declaration-link rows include referenced declarations and do
not count distinct theorems defined by this module.

The generation receipt is
`/tmp/darwin-cfsg-inverse-transpose-generation-v4.json`, digest
`73e990c15b4274a0783703e54dc3d8db6db8ee61a82c39b6890383d9467262a0`.
Its complete coverage means **one explicitly selected source out of one**,
not full CFSGPort or repository coverage. This verifies capture → structural
DNA → fossil overlay → generation receipt locally. It does not establish live
Arango ingestion, lossless expression reconstruction, taxonomy accuracy, or
Yang–Mills capture scalability.

### Full inventory recheck with Git fossils

The selected Yang–Mills scan exposed a scope leak: the Python dependency oracle
added 1,509 Python-import and 252 test-import edges unrelated to the selected
Lean source. The scanner now restricts Python edge origins to inventory paths
and marks out-of-inventory destinations explicitly. A fresh run at
`/tmp/darwin-yangmills-map-scopefix.json.gz` retained the same stable selected
source digest and 15 lexical declaration candidates, with exactly three local
imports crossing its inventory boundary and one external-package import; no
unrelated Python edges remained. The matching Git event stream is
`/tmp/darwin-yangmills-fossils-scopefix.jsonl`. This is runtime evidence for scope
correctness, not compiler-DNA coverage. The scanner and batch-export suites
subsequently passed all 50 tests in Sage under the shared execution lock.

The Yang–Mills capture at `/tmp/darwin-yangmills-capture-20261030-recheck`
timed out after 602.23 seconds with no validated DNA output. Its failure-report
serialization then raised `TypeError: Object of type bytes is not JSON
serializable`: `TimeoutExpired` diagnostics can be bytes despite `text=True`.
The diagnostic-tail helper now decodes those bytes with UTF-8 replacement before
serialization. An end-to-end mocked timeout test verifies that the batch writes
a JSON failure report, retains both diagnostic streams, counts zero valid
captures, and exits unsuccessfully. The original failed run has no batch report;
this audit records its terminal output, not a retroactively successful capture.
Capture performance remains unresolved and requires phase-level diagnosis before
another expensive retry.

Phase diagnostics were subsequently added to `DAG.RawInfoTreeExport` and the
locked `DAG.RawInfoTreeExport` target built successfully. The diagnostic run
logged completion of import loading and command elaboration, then began walking
27 InfoTree roots. Repeated live observations showed traversal at root index 7;
this establishes that elaboration completed, but is not a per-function profile.
The live log is `/tmp/darwin-yangmills-phase-diagnostic.log` and its output path
is `/tmp/darwin-yangmills-phase-diagnostic`. This direct diagnostic invocation
does not attach the batch source/context receipt and must not be accepted as
source-bound DNA merely because row files eventually appear.

Inspection identified redundant hashing in `mctxDeclRows` and `lctxDeclRows`:
each type/assignment/value digest is computed for its full digest field and
again through `exprProjectionWithLctx` for the `t_` plus 40-character display
field. Reusing the already computed digest preserves that field's definition
and has now been applied at those four projection sites. Generic Lean
equivalence checks in `tests/RawInfoTreeProjectionTests.lean` compare the reused
digest projections to the original expression projections, including absent
optional values. The locked exporter build and those checks are queued behind
the active baseline capture; compilation and performance effects are not yet
verified. The baseline was subsequently observed advancing to root index 8.

Partial-inventory topology inspection also found that `repoImportOutDegree`
dropped known repository imports when the destination was outside the selected
inventory. Counting now occurs before the internal-endpoint check; external
package imports remain excluded from this local repository degree. A focused
regression covers two selected modules with a shared unselected local import
and a separate Mathlib import. This additional regression is pending execution
after the active capture/build lane; the earlier 50-test result predates it.
The baseline capture has since reached root index 10 of 27.

### Context deduplication integrity debt

The downstream fingerprint contract is now `raw_infotree_structural_dna.v4`:
the exporter source digest participates in the DNA fingerprint, and generation
validation requires a well-formed receipt and verifies that binding. Legacy v3
records require re-extraction; changing their version label is insufficient.
Fossil overlay construction checks the producer digest against both raw capture
provenance and current exporter bytes. Generation validation alone establishes
record integrity, not current producer freshness; fresh extraction and the
overlay perform the filesystem comparison. Seven consumer suites passed 107
tests before adding three explicit missing/tampered/legacy receipt regressions;
the complete generation-manifest suite then passed all 28 tests. No new runtime
DNA coverage or model accuracy is claimed by this format migration.

DNA extraction now checks `exporterSourceSha256` against the current repository
exporter before Lean-context inspection. Unknown or changed producers yield no
feature row and an audited `exporter_source_missing_or_stale` rejection. Accepted
rows retain the exporter digest as provenance metadata. Regression coverage
includes missing receipts, changed exporter bytes, absent exporter files, and
the existing source/context rejection paths. The four DNA, fossil-overlay,
generation-manifest, and batch-export suites passed all 67 tests in Sage under
the shared lock. This gate protects fresh extraction; previously serialized
DNA rows still require producer-receipt enforcement in downstream generation
validation. The structural feature fingerprint format is unchanged in this step.

Batch capture receipts now include `exporterSourceSha256`. Resume rejects
missing/stale exporter-source receipts while preserving the old capture, and
capture completion withholds provenance if the exporter source changed during
the run. This prevents automatic resume from recycling pre-repair captures
under a changed exporter. Fifteen batch-export tests pass in Sage, including
current/stale/missing receipts and exporter changes during capture. This digest
binds the exporter source file only; it is not a receipt for its entire imported
implementation. Downstream DNA compatibility policy still needs to consume this
producer evidence explicitly before old and new captures can be treated as
comparable observations.

Metavariable declaration-row sharing is now repaired for newly generated
captures as well. `mctxIdentityKeys` compares root-scoped arrays containing
declaration metadata, exact structural types, optional exact assignments, and
the structural local-context identities above. Delayed-assignment pending IDs
and counts are included to match the exported projection. The abbreviated
signature contributes only to the output key; a unique ordinal disambiguates
distinct content even when abbreviated signatures collide. This is identity
of the exported declaration projection, not serialization of all internal
metavariable/universe state.

The locked exporter build and `RawInfoTreeProjectionTests.lean` passed after
this change. Regression fixtures demonstrate the old same-ID/different-type
signature collision and check type changes, assignment changes, and repeated
snapshots: five references retain four distinct declaration rows and the
repeated snapshot reuses its key. Earlier local-context and projection tests
also pass. Older captures retain their original limitations; fresh large-scope
capture performance and DNA coverage remain unverified.

The local-context part is now repaired for newly generated captures.
`lctxIdentityKeys` uses a root-scoped structural key containing context size,
declaration metadata, exact `ExprStructEq` types, and optional let values.
Metadata includes binder information, nondependency flags, and auxiliary names.
The old abbreviated signature only contributes to a display key with a unique
ordinal; it no longer decides whether rows are suppressed. Hash-map collisions
are resolved by structural equality. Existing captures are not retroactively
repaired. Metavariable-context deduplication remains unresolved.

The locked exporter build passed. `tests/RawInfoTreeProjectionTests.lean`
also passed, exercising a same-variable type change, distinct let values, and
repeated identical snapshots: five references retain four context declarations,
with the repeated snapshot sharing its original key. Its generic projection
equivalence checks continue to pass. No large-capture speedup is claimed.

After explicit user authorization, the baseline diagnostic was interrupted at
root index 10 with exit code 130. Its log and output directory were preserved;
it produced no validated DNA. The queued locked exporter build then passed,
and `tests/RawInfoTreeProjectionTests.lean` checked successfully. Both generic
projection equivalences are therefore kernel-checked for the digest-reuse
change. The Sage scanner/batch regression suites subsequently passed all 51
tests under the shared lock, including the partial-inventory degree regression.
These results supersede the pending-verification notes above. Performance gain
and the context-deduplication issue below remain unverified/unresolved.

Source review found a concrete distinction between declaration fingerprints and
the exporter's context-table deduplication keys. `lctxSignature` includes index,
free-variable ID, user name, declaration kind, and let status, but omits the
declaration type and let value. `emitLctxRef` hashes this signature and suppresses
declaration rows for a previously seen key. Lean 4.34.1's
`Lean/LocalContext.lean` exposes `LocalContext.setType` via `modifyLocalDecl`, so
type changes need not change the fields in this key. Distinct context snapshots
can therefore share a deduplication signature even without a hash collision.
`mctxSignature` likewise omits declaration types and uses native expression
hashes for assignments. These are not the SHA-256 de Bruijn declaration digests.

This is an unresolved source-level integrity risk, not a measured occurrence in
the active Yang–Mills capture. Existing output remains explicitly partial.
Repair requires content-sensitive context identity and regression cases for
type/value changes, while retaining sharing and avoiding recomputation of every
context row at every reference. Validator cardinality checks alone cannot
recover rows already suppressed by the exporter. Performance optimization must
not promote these context keys to semantic or content identity.

The subsequent capture-entrypoint check found a Python compatibility regression
in `batch_raw_infotree_export.py`: a multiline replacement expression inside a
single-line f-string prevented the system Python from parsing the script.
The directory-name expression now uses ordinary parenthesized concatenation.
The existing CLI regression test runs both the Sage interpreter and available
`/usr/bin/python3`, so Sage's newer parser cannot mask this entrypoint failure.
All 10 batch-export tests passed in the Sage environment after the repair;
this validates capture orchestration, not repository-wide InfoTree coverage.

The maintained scanner was run with Python dependency analysis and `--git-history`,
writing `/tmp/darwin-current-full-20261030-recheck.json.gz`. It observed 42,083
paths, 25,932 `lean_source` rows, 91,631 local Lean import edges, and 246,708
lexical declaration candidates. These are observed mixed-scan counts: 36 paths
changed during the run, including CFSGPort sources, PeirceSpine/Supercharge,
AI Studio extraction caches, and the extraction script. The complete changed-path
set is recorded with digest
`544bce24cdf02fe6ed4b6e6c99dd70eabc58c054b6091606c238e7c86e29b063`.
This run therefore cannot certify a coherent whole-repository generation.

Three current Lean paths remain outside the inferred Lake module index:
`lean/AuditNative.lean`, `lean/AuditStrict.lean`, and
`lean/KaplanskyCliffordBridge.lean`. They remain inventoried with Git path
fossils; adding them to a build requires inspecting their actual role and imports.
The single import-parser diagnostic is in an archived source containing prose
on an import line. The scanner correctly withholds guessed module edges.

Compiler metadata still lacks source/olean generation hashes and is rejected:
zero compiler fingerprint files and zero current-DNA-to-fossil joins were
accepted. The next integration requirement is a source-bound current compiler
capture, followed by source-hash-verified review and overlay generation.
Repeated scans alone cannot supply that missing evidence or reviewed labels.

The source-first inventory now keeps its broad `repository_evolution_analysis`
role and adds an explicit component taxonomy for maintained pipeline entrypoints:
source inventory, generation provenance, current InfoTree fingerprints, Git
lineage, reviewed-label flow, graph analysis, training, and visualization.
Unmapped future entrypoints receive `uncertain_unmapped_entrypoint`; they are
not folded into a guessed component. A fresh scoped scan of the 19 Python
modules in `tools/repository_evolution/` was stable and mapped all 19 to
distinct components. This is a scoped implementation check, not whole-repo
classification evidence. Two full scans during the same work period detected
three changing paths each and are therefore excluded from global generation
claims; both also confirmed that the existing compiler DAG metadata is stale
for the current source set and joined zero fingerprint files.

The scanner and generation receipt now retain and digest the complete set of
paths that changed during a scan instead of keeping only a 20-path sample.
This lets a selected current-Lean-source scope prove it excludes every
observed in-flight edit, even when the worktree scan as a whole is unstable.
It does not turn the mixed global scan into a complete repository generation;
the scoped source hashes and capture coverage remain the authority for each
selected module set.

On 2026-10-30, a fresh full scanner run covered 42,009 paths and 25,891 Lean
sources, and identified three changing paths with the complete path-set digest.
The compiler DAG was stale for that source set, so zero compiler fingerprint
files were joined. The unchanged `CartanMovingFrameSE3HelicalBridge.lean` pilot
was then independently bound as a one-source scope disjoint from those changes:
1/1 DNA source, 1,534 InfoTree node links, 387 declaration-to-line links, and
four source-line fossil spans. The independently recomputed generation receipt
validated. Its history relation remains module-path cohabitation: 113 current
lines map to two commits; this is not historical theorem identity or complete
repository DNA coverage.

## Implementation delta — 2026-10-29

The InfoTree capture, Lean context fingerprint, DNA, and Git fossil join now
preserve lexical source identity for in-repository symlinks, matching the
scanner's Lake module identity rule. The symlink target supplies source bytes,
while the taxonomy/fossil key and selected `.olean` remain bound to the path
Lake compiles. Regression coverage exercises discovery, `.olean` selection,
context metadata, DNA identity, and overlay source normalization.

Reviewed corpus holdouts now use deterministic iterative multi-label
stratification over indivisible module/owner/exact-content groups, following
the multi-label split principle of Sechidis, Tsoumakas, and Vlahavas (2011).
The readiness gate remains authoritative for inadequate per-label support; the
splitter does not claim to make an undersized or highly clustered corpus
evaluable.

Taxonomy materialization now requires at least two distinct reviewer IDs to
agree on the complete label set before promoting an annotation. Exact-set and
Jaccard agreement are reported as descriptive measures; disagreements and
single-reviewer cases do not become training labels. Complete empty label sets
are represented as valid negatives, so a reviewed artifact need not be forced
into an archetype that does not apply.

The current worktree now includes a generation-checked current InfoTree to Git
path-fossil overlay and append-only Arango staging in
`tools/infra/arango_git_fossil_overlay_ingest.py`. The bounded
`lean/DAG/Basic.lean` pilot is persisted in `infogeometry`: 3,172 node links,
8 path events, 1 shared path fossil, exact live counts, and zero dangling
endpoints. Its RawInfoTree capture is partial (17 roots and 10,771 leakage
rows), and all links mean module-path cohabitation only. Focused Sage pytest
verification passed 9 tests across the Arango raw importer, fossil overlay,
and new overlay staging preflight. This confirms the pilot path, not a
repository-wide taxonomy or learned classifier; see the blueprint for the
remaining coverage and model gates.

The overlay now joins byte spans from the current RawInfoTree export to a
generation-bound shared Git line-origin stream (`git blame --contents` at the
captured HEAD). Uncommitted lines are explicit zero-SHA evidence; symlink
aliases and unavailable blame are marked without claiming target-path history.
Arango staging validates the line-stream hash and references, stores shared
line-fossil documents, and adds current-node-to-line-origin edges. It also
emits current declaration-occurrence records carrying `declKey`, `linkKey`, and
the same shared line-fossil references; Arango adds declaration-link-to-line
edges. `declKey` follows the existing `DAG.Schema` stable declaration-name
key, so this can join the current declaration DAG by key. These links describe
overlap with current lines and their Git attribution, not a historical
declaration identity. Arango preflight recomputes summary counts from the
shared line/declaration streams and rejects mismatches. The Sage pytest run
passes 117 tests across the evolution, reviewed-taxonomy, lineage, and Arango
staging suites. No new generation was written to Arango; the persisted
one-module pilot does not yet include these line-origin collections.

Repo-grounded concept distinction: `InfoGeometry.LLM.KMSSoftmaxBridge` proves
the finite router softmax/Gibbs identity and normalization, while
`InfoGeometry.QuantumContext.AttentionKMSState` and
`AttentionGNSBridge` provide finite attention-state and algebraic GNS
constructions with stated scope limits. The Python `local_attention` routine
is lexical DAG navigation, not the formal KMS state or learned transformer
attention. These are separate typed artifacts for taxonomy, with no assumed
equivalence between them.

The current taxonomy feature extractor now consumes generation-bound source
lineage summaries when supplied. It uses attribution status, binned line and
declaration coverage fractions, and coarse line / commit / origin-path counts;
it excludes commit hashes, author times, messages, and source paths. Model
feature version is `repository_taxonomy_features.v4`, and a model whose
vocabulary uses these features requires the matching overlay at inference.
Trainer feature selection remains train-group-only and reports a same-split
`sourceAndStructureWithoutGitLineage` ablation. This is current-snapshot
classification evidence; it does not provide time-held-out historical
classification or prove a performance improvement before evaluation.

## Earlier stable repository-wide inventory — pre-Lake-package resolver

The current scanner completed over the full tracked/non-ignored worktree at
`/tmp/current-full-refactoring-map-2026-10-29.json.gz`. It observed 41,934
paths, with zero path-state changes during the scan; Git path summaries resolve
to the same `HEAD` (`033fbf0e6fc61a8c24c825ab39ad480460804a85`). The worktree
was dirty, so this is a stable snapshot of the current staged/unstaged source,
not a claim that the inventory equals the checked-out commit tree. The scan
stored compact per-path Git continuity summaries and no expanded commit-event
ledger.

The scanner observed 25,859 Lean source paths, 87,028 local Lean import edges,
1,451 Python import edges, and 244,871 lexical Lean declaration candidates.
These declaration headers are not Lean-parser or kernel evidence. The
uncertainty count of 4,182 decomposes into 2,998 generic source paths and
1,184 Lean candidates outside the package source root. A further 21 in-package
Lean files have no owner inferred from the parsed Lake roots/import closure.
The 33,048 imports without a repo source path include external/dependency
imports; they are retained as unresolved edges rather than treated as missing
repository files.

Compiler DAG metadata at `artifacts/dag/index/meta.json` is stale for this
source snapshot: its recorded source hash differs from the scanner's current
Lean source hash. The scanner correctly marks the fingerprint generation
`stale_source_generation`; those declaration/edge rows were not joined. This
inventory is usable for current path/import/build-boundary taxonomy and Git
path navigation, but compiler-derived declaration DNA requires a fresh,
source-bound export before it can be joined to the full snapshot.

The same scan motivated a role-boundary refinement: Eigen's vendored source,
the CUDA backend, formalization support, symbolic witnesses, and `src/igf` had
been left in a generic unclassified-source bucket. After adding path-evidence
roles, a stable full scan reduced that bucket's uncertainty from 4,182 files
to 116 (33 generic source paths plus 83 Lean files outside recognized package
roots). This is a measured baseline for that scanner revision. Subsequent
Lake-package support changed source ownership logic, and repeated full scans
then observed concurrent source/worktree edits; their owner counts are not
reported as current inventory facts.

The scanner now reads manifest-declared local Lake path packages and limits
module discovery to declared target roots/globs plus same-package import
closure. This resolves the repo-owned `InfoGeometryCore.Basic` import through
`lib/InfoGeometryCore` and avoids treating every Lean file under a broad
`srcDir := "."` as part of the `proofs` target. Synthetic regressions cover
both the path-package dependency and this broad-source-root boundary. The
older full scans after that change had observed concurrent worktree edits.

## Stable full-worktree scan snapshot — 2026-10-29

At that scan, the updated scanner completed over 41,999 tracked/non-ignored
paths with no path changes during extraction. It recorded `HEAD`
`033fbf0e6fc61a8c24c825ab39ad480460804a85`, the worktree was dirty but stable,
and Git path summaries resolved to that same revision. The snapshot manifest is
`72ccb84e40cc524bec0d2977b590cf290e603328fbbf92cac1c6534a2e90b6c0`. The full
report is `/tmp/darwin-refactor-map-20261029-verified.json.gz`.

The scan observed 25,885 Lake-indexed Lean source paths, 245,937 lexical
declaration-header candidates, 91,503 repo Lean import edges, 35,179 pinned
external-package import edges, 1,500 Python import edges, and 48 Lean imports
without a located source. These are source/navigation counts: declaration
headers are not parser or kernel evidence, and external/toolchain edges are
kept distinct from repo-source imports. Git history has path events for 41,860
of the 41,999 current paths; each record is path-continuity metadata, not a
historical content fingerprint.

The existing declaration index remains stale: recorded Lean source hash
`7eb46ad5100c93bcbc5fcc137cddfa00d931fd20b0fb268ef7ed0d8a36c72d55` differs
from current hash
`900aa44e2ffe590e78a0a7cffd37154883e8594c8a85fa27f695808f86b47624`. The
scanner joined zero compiler fingerprint files and correctly kept cached
declaration DNA unjoined. The attempted locked `InfoGeometry.All` build failed
in `lean/InfoGeometry/Exceptional/CFSGPort/CurtisTitsRankOne.lean`; this stable
source/history scan does not supply a fresh compiler export. Focused Sage test
suites passed 79 scanner/artifact/feature tests and 58 downstream manifest,
corpus, fossil-overlay, attention, and reviewed-training tests.

Several subsequent whole-worktree scans observed concurrent edits to
`lean/InfoGeometry/Algebra/Zorn/G2FullPeelWeylObstruction.lean`,
`lean/InfoGeometry/NCG/ReflectedAssociatorResidual.lean`,
`lean/Omega/Conclusion/RealInput40NoUniformRHResidueLaw.lean`, and
`lean/InfoGeometry/PureNonCommutativeOperatorSpine.lean`. The latest scan
at that time reported `worktreeConsistentDuringScan: false` and a source hash of
`d9f43f5cd1a5f525bed0259133eed5e0e3d97b7b85a0bb7ba2531831e7bb856f`; treat the
earlier `72ccb...` report as its own source snapshot, not as a receipt for a
later worktree state.

## Fresh stable full-worktree scan — 2026-10-29

A new offline scan completed with `--no-python-cpg --git-history` and observed
41,999 paths, zero path changes during extraction, and the same `HEAD`
`033fbf0e6fc61a8c24c825ab39ad480460804a85`. Its source manifest is
`461420917f9a71628a0bd5fab9a915ee0f7f201db98b4b2fbc767c6e8112b8d9`; the
filesystem-topology digest is
`e9c8cf126e5ce9e35791c013bd4f7742c0eff1aedfa2cb97e282118bf27013e8`. The
report is `/tmp/darwin-refactor-map-current-20261029.json.gz`. This is a
stable dirty-worktree snapshot, not the committed `HEAD` tree, and it is the
first stable receipt for the source hash that earlier attempts had sampled
while the worktree was changing.

This run counted 25,885 Lake-indexed Lean source paths, 245,943 lexical
declaration candidates, 91,504 repo Lean import edges, 35,179 pinned external
package imports, and 68 external-reference imports. Python AST dependency
extraction was disabled in this run; the preceding stable scan counted 1,500
Python import edges. This run found 17 uncertain file classifications, 3
uncertain build-ownership cases, 3 unindexed Lean sources, and 48 imports
without a located repo source. These remain typed navigation/count evidence;
the lexical declarations are not Lean parser or kernel output.

The declaration export is still stale for this snapshot: metadata source hash
`7eb46ad5100c93bcbc5fcc137cddfa00d931fd20b0fb268ef7ed0d8a36c72d55` differs
from current source hash
`d9f43f5cd1a5f525bed0259133eed5e0e3d97b7b85a0bb7ba2531831e7bb856f`. Therefore
zero compiler fingerprint files and zero current-DNA-to-fossil links were
joined. Git path history is available for 41,860 paths, but remains path
continuity evidence only. The focused Sage suites for scanner, artifact
receipts, taxonomy features/training, manifests, reviewed labels, fossil
overlays, and attention passed 137 tests. The previously attempted full Lean
build still failed in the separate `CFSGPort/CurtisTitsRankOne.lean` owner;
no compiler export was refreshed by this scan.

### Refresh transaction lock and source-edit rejection — 2026-10-29

An attempted temporary compiler refresh exposed a race in the maintained
`refresh_decl_graph.py`: source and `.olean` inventories were hashed before the
refresh acquired the shared build lock. A concurrent build changed the `.olean`
inventory during hashing, and the refresh aborted before exporting. The refresh
now acquires the shared lock before its first hash and holds it through optional
prebuild, indexing, post-export hashes, and metadata stamping. The prebuild
re-enters the same lock object; nested build cleanup preserves the caller's lock
reference, and cache-hydration exceptions release their nested reference.

The locked build of `dagIndexer` plus `InfoGeometry.Physics.All` then completed
successfully (13,048 Lake targets). The indexer exported 38,329 declarations
and 267,975 edges to `/tmp`, but the refresh correctly refused to stamp that
artifact because the Lean source inventory changed during its 113-second export.
The temporary rows therefore remain unjoined and are not a current DNA receipt.
The same interval's full-worktree scan observed changes to
`lean/InfoGeometry/Algebra/SteinbergBraidDefectSpine.lean`,
`lean/InfoGeometry/Exceptional/CFSGPort/ChevalleyNormalizerTriviality.lean`,
and `lean/InfoGeometry/PureNonCommutativeOperatorSpine.lean`; it marked the
snapshot inconsistent and did not join compiler fingerprints or fossil links.
Focused Sage verification of the lock, refresh, scanner, and output-receipt
tests passed 84 tests. Thus the build-lock race is repaired and tested, while a
source-stable full compiler export remains outstanding.

### Unindexed Lean source review — bounded snapshot, 2026-10-29

The earlier full scan surfaced three unindexed Lean paths; they were checked
in a bounded scan and remain the same three unindexed candidates in the latest
stable full scan:

```sh
python3 tools/repository_evolution/refactoring_map.py --no-python-cpg \
  --path lakefile.lean \
  --path lean/AuditNative.lean \
  --path lean/AuditStrict.lean \
  --path lean/KaplanskyCliffordBridge.lean \
  --out /tmp/unindexed-lean-review-v2.json.gz
```

The selected four-path source manifest was stable during that scan
(`0cf83208…3298`). Each Lean file remains outside the Lake module index, but
the map now preserves its lexical `moduleCandidate` and source imports;
neither signal grants build ownership. `AuditNative` and `AuditStrict` both
import `InfoGeometry.Canonical.All` and `InfoGeometry.Meta.Architecture`, while
`AuditNative` invokes `#audit_architecture`. The separate audit-pipeline test
claims `AuditStrict` should avoid the canonical umbrella, so current source and
test contract conflict. `KaplanskyCliffordBridge` has no matching references
in the searched Lakefile, test, tool, script, documentation, or CI paths; its
bounded import graph reports one unresolved module name,
`Mathlib.LinearAlgebra.Finrank`. Its Git history is fossil context only and
does not resolve whether the file is an active mathematical artifact or an
orphan candidate.

A current five-path scan around `lean/InfoGeometry/BottPeriodicityReconciliation.lean`
was stable and resolved all of that module's imports by evidence class: one
repo source outside the selected inventory, one `InfoGeometryCore` local
path-package source, and six Mathlib sources in the existing
`.lake/packages/mathlib` cache pinned by the manifest at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. These are typed navigation edges;
they do not certify that the current stale declaration-DAG cache matches the
source. Import extraction strips nested block and line comments, avoiding
false edges from prose examples; pinned external package sources are resolved
through the existing Lake cache and retain their manifest revision. The
package/source-root resolver and selected-scope distinction pass the focused
33-test Sage suite. A subsequent repository-wide attempt again detected a
Lean source edit during scanning and is therefore not used as an aggregate
inventory; the bounded scan is the authoritative evidence for this join.

### Lean import parser and external-reference resolution — 2026-10-29

A first full inventory was stable for all 41,980 included paths, but its
ASCII-only import tokenizer split Unicode module names such as
`ZornVectorMatrixMöbiusAction` and emitted false unresolved-module edges. It
also did not resolve sources inside gitlink-bounded `external_refs` trees. The
scanner now accepts Unicode identifiers and Lean quoted identifiers, withholds
path-like unsupported forms as parse diagnostics, and resolves a direct module
path inside an external-ref boundary without indexing or modifying that
submodule. The external edge carries the imported source content hash.

Focused verification over nine selected paths was stable and produced zero
unresolved imports and zero import parse diagnostics. It resolved the quoted
`proofs.BraidProject.Basic` import and the Unicode Möbius imports, and resolved
`GIFT.Algebraic.Octonions` to
`external_refs/gift-framework-core/GIFT/Algebraic/Octonions.lean` with its
content SHA-256. This corrects the prior scanner's false orphan classification
for that import.

The subsequent full scan used scanner SHA-256
`47658efd0996b14e3d468cac211c96e1f5e65d6632ebe4e2bebfb9a6e4e7925e` and
matched it against the current scanner source. It covered 41,980 paths with a
stable, dirty worktree snapshot (manifest
`fe4d1ef481a81d73c69fbb2bfb5d46d856bd658c95d0d6126689660d291ded1f`) and
reported 25,869 Lean source paths, 245,382 lexical declaration candidates,
34,052 pinned dependency imports, 65 external-reference imports, and zero
unresolved import edges. One malformed import-like prose line remains
diagnostic-only in an archived source. Python AST scanning was disabled, so
this pass supplies no Python dependency counts.

Twenty-five Lean files are outside the declared Lake root/import closure and
have no observed inbound Lean imports; this is an unowned/unreferenced review
set, not proof of dead code. Seventeen more `.lean` files are outside
recognized package source roots. Before cleanup, inspect direct Lake build
targets plus shell/Python/CI/test references. Compiler DAG metadata is still
stale for this snapshot and remains unjoined.

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

At the time of the source audit, the tracked Arango Darwin path
(`tools/infra/darwin_commit_graph.py`, `darwin_commit_taxonomy.py`,
`darwin_evolution_algorithms.py`) stored commit history and optional
commit/declaration links in `darwin_commits`; its links were resolved against
the current `infogeometry.decls`, and its Linnaean rank was heuristic. The
rank model has since been removed from the current writer and reports. Current
change labels are multi-label `weak-rule-v3` facets, not a hierarchy. The
current graph writer stores parent-to-child Git edges in
`commit_parent_edges_v2`; old `commit_edges` and `taxonomy_ranks` collections
are intentionally left untouched. Declaration links remain navigation
evidence, not historical declaration snapshots or semantic species.

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
  - At the audit revision, imported commit nodes, child-to-parent edges, and
    heuristic rank records. The current writer instead streams path metadata,
    emits ordered parent-to-child edges in `commit_parent_edges_v2`, and adds
    evidence-bearing non-hierarchical change facets; it leaves the old edge
    and rank collections untouched.
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

The optional cross-database bridge and browser visualizer listed below were
ignored local files at the source-audit revision; their current tracking state
is separate from the rank-model correction.

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
- `tools/infra/evolution_taxonomy.py` assigned multi-label weak commit-change
  categories from message and path regexes (`weak-rule-v2`) at the audit
  revision. The current schema is `weak-rule-v3`; its rule-weight field is not
  a calibrated probability.
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

### Source-first refactoring map (implemented)

`tools/repository_evolution/refactoring_map.py` composes a read-only worktree
inventory from Git's tracked/non-ignored path list, source imports, static Lake
target declarations, the existing Python AST dependency oracle, and lexical
Lean declaration headers. It does not connect to ArangoDB, copy source files,
or refresh compiler artifacts. Run it with:

```bash
python3 tools/repository_evolution/refactoring_map.py \
  --out /tmp/refactoring-map.json.gz
```

Add `--git-history` when path-change fossils are needed. This reuses the
existing Git `name-status` extraction contract and summarizes the commits
reachable from `HEAD` into per-current-path touch counts, status histograms,
recent commit samples, and reverse rename-path candidates. It streams commit
metadata without checking out old trees or retaining a commit-by-file dump.
The lineage label remains `path_continuity_candidate_not_content_identity`;
commit touches and rename similarity do not establish that the current source
is semantically identical to every historical path version.

The report carries a content-manifest hash and records worktree dirtiness. Its
axes are independent: artifact role, path/build ownership candidate, typed
source dependency, and weak commit-change label. The Lakefile parser strips
Lean comments, bounds each list to its matching closing bracket, keeps all
three glob forms (`one`, `andSubmodules`, and `submodules`) distinct, and marks
unrecognized glob syntax as a partial parse. Local import closure provides
additional target-membership evidence. Source import edges are retained for
all Lean candidates under declared source roots, including modules outside a
target's root/import closure; those edges do not grant Lake build ownership.
Such a path may carry a `moduleCandidate` derived from its lexical location,
and its source-root identity, separately from `module`, which is reserved for
the Lake-indexed module map. The review queue carries that candidate context;
the corpus uses it only to keep candidate-module peers in the same evaluation
split, while uncertain owner placeholders fall back to path grouping. Unresolved
Lean import totals are also stratified by the importing file's source role, so
historical/sandbox imports do not silently read as active-module build failures.
this is a static build-boundary candidate, not proof that a target builds.
It captures path identities and repository path membership before and after the
scan; file edits, additions, and removals during extraction invalidate the
snapshot.
Lexical declaration candidates include source line, declaration kind/name,
namespace context, and inherited build-target candidates. They are explicitly
marked `lexical_candidate_not_lean_parser_output`; only compiler exporter rows
can promote that data to compiler-observed declaration records.

The scanner also emits a deterministic coarse graph grouped by unique Lake
target or, where target ownership is ambiguous, by the first two directory
components (or the sole directory for shallow paths). Internal and boundary edge counts retain edge kinds. Matching
lexical declaration-kind counts, repository import out-degree, and Lake target
membership form structural cohort candidates. They are retrieval/topology
hypotheses, not named mathematical archetypes or semantic equivalences. The
existing `wire_topology_transform.py` SCC overlay and
`arango_wire_topology_ingest.py` archetype hash bundles remain the compiler-DAG
owners; this scanner does not replace them.

The current `arango_causal_memory.local_attention` is a bounded lexical token
matcher with hand-set name/module/kind weights. It is useful for navigation,
but it is not a trained attention head and does not produce a Gibbs kernel.
`tools/attention_polytope.py` verifies exact properties of supplied stochastic
matrices; it is not a model trainer. Any learned edge attention and label head
must be a separately versioned layer over the observed graph.

`tools/repository_evolution/attention_scc.py` implements the postprocessing
contract for edge scores. `edge_attention_baseline.py` now supplies a
deterministic, untrained endpoint-cosine baseline from source-hash-bound
embedding packets; it requires vectors for every local dependency endpoint
and binds scores to exact typed edge witnesses. The postprocessor checks source
snapshot equality and complete coverage of the declared typed-edge scope, applies numerically
stable per-source Gibbs normalization, sparsifies by declared top-k or
minimum-probability support, and emits SCC membership plus the quotient graph
with source-edge witnesses. Cosine affinity is a navigation baseline, not a
causal or semantic explanation. The shared iterative Tarjan routine is
`tools/infra/graph_components.py`, also used by
`darwin_evolution_algorithms.py`.

The mathematical KMS/GNS attention substrate already exists in
`lean/InfoGeometry/QuantumContext/AttentionKMSState.lean`, with the quotient
action and cyclicity boundary in `AttentionGNSBridge.lean`. It proves a finite
softmax-weighted matrix state, GNS expectation/quadratic identities, faithfulness
for full-support weights, a finite KMS trace boundary identity, and modular
Tomita identities. The observable matrices are noncommutative; the reference
density is diagonal. `edge_attention_baseline.py` now creates source-embedding
and lossless InfoTree-feature cosine packets, with the latter restricted to the
Lean-import edge layer and bound to the current generation manifest. These are
deterministic affinity baselines, not trained attention. A trained
state-conditioned graph model still needs a reviewed edge-ranking objective,
an explicit feature-to-logit map, and held-out evaluation; the existing KMS/GNS
theorems alone do not identify dependencies with observables or certify
semantic attention.

The scanner reuses `tools.infra.build.compute_lean_source_hash` to compare the
compiler artifact's stamped source hash with the current Lake source inventory.
In the audited worktree that check found the artifact stale
(`7eb46ad5…` recorded versus `012cdee5…` current), so the report marks it
`stale_source_generation` and refuses the join. A source-hash match alone does
not promote declaration fingerprints. The maintained refresh path now stamps
SHA-256 hashes for declaration, edge, morphism, type, full-graph, and
structural-topology outputs. The scanner joins per-file de Bruijn-v4 summaries
only after matching current source and `.olean` hashes, declaration/edge output
hashes, schema version, and exported row counts. Legacy metadata without those
output hashes remains unjoined. Joined digest cohorts are navigation candidates,
not semantic equivalence. External imports are reported as
imports without a matching repo source file, not as errors.
When Git path fossils are enabled, a file-level `evolutionaryLineage` record
joins the verified current fingerprint summary and Git name-status history by
current path, explicitly as continuity evidence rather than historical content
identity. No old repository trees are materialized.
Python roles retain the existing oracle's heuristic status and dynamic-import
limitations. Files under agent sandboxes, recovery areas, and archives are
included but labeled as out-of-scope candidates instead of being silently
treated as production Lean source. The same path evidence now marks
`tools/multisystem/major_restore_non_overwriting` as a recovery workspace;
its Lean files do not inflate the live tool/library taxonomy.

Focused verification: `tests/test_refactoring_map.py` exercises classification
uncertainty, Lake roots/globs, source import and target joins, lexical
declaration candidate status, coarse grouping, fingerprint provenance, and
tampered-export rejection. `tests/test_artifacts.py` covers output-hash
stamping. Run both in the Sage environment after the shared locked build exits.

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
6. **Structural affinity:** algorithm-versioned type/value/de Bruijn markers,
   SCC topology, and graph neighborhood features; candidate similarity only.
7. **Formal status:** source declaration, kernel-checked result, assumptions,
   or audit status, derived only from compiler/build evidence and not from a
   taxonomy model.

Each label should carry source commit or snapshot ID, file/range or graph row
key, extractor version, rule/model version, evidence references, and a status
such as `observed`, `weak_rule`, `model_candidate`, or `kernel_checked`.
Never merge these statuses into a single “species confidence.”

### Attention and SCC contract for the future model layer

The small codebase model should produce two distinct outputs: (a) per-artifact
scores over reviewed archetype labels, and (b) per-edge attention logits over
the existing typed dependency neighborhood. For outgoing edge logits
`s(u,v)`, Gibbs factors are
`pβ(v|u) = exp(β s(u,v)) / Σw exp(β s(u,w))`. Record temperature, model and
feature versions, candidate neighborhood, and input snapshot hash. To obtain
attention SCCs, first define a sparse support rule such as top-k edges per node
or a preregistered minimum probability; a full softmax is strictly positive
and therefore preserves the original graph's SCC partition. Store raw edge
witnesses, normalized factors, and the support rule, then contract SCCs and
retain the quotient DAG. SCC and label outputs remain model-derived navigation
evidence. Evaluate label calibration and edge ranking on held-out modules and
commits, with commit-message/path leakage controls, before giving the scores
semantic names.

## Development plan (reuses existing owners)

1. **Specify the current-sample producer contract** using the existing
   `repo-dna-snapshots/v1` consumer expectations: current source hash,
   toolchain/manifest fingerprint, generation ID, declaration key/name, native
   `typeDigest`/`valueDigest`, algorithm versions, and InfoTree root/coverage
   references. A manifest is provenance metadata, not independent verification.
2. **Build and capture the current worktree once.** Compile the current source
   under the pinned environment through the shared build lock and run the
   native Lean exporters. Do not clone, check out, or compile every Git
   revision. Record failures and partial coverage explicitly; never label
   failed or uncompiled observations as DNA.
3. **Attach Git fossil metadata without reconstructing old source trees.**
   Stream commit ancestry and path/numstat events, link them to current files
   as path-continuity candidates, and keep declaration/InfoTree links at
   module-path cohabitation unless an exact edit witness exists. Join current
   InfoTree observations only within their source/build generation, keyed by
   `(generation, rootKey, nodeKey)` and declaration span/key. Retain raw rows,
   coverage, and leakage; never join node IDs across runs.
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
   promote similarity to ancestry/equivalence. GPU training remains gated on
   the current-source receipt, InfoTree coverage/join, fossil-link semantics,
   and append-only generation validation.
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

## Current full inventory and KMS/GNS/attention taxonomy slice — 2026-10-30

A fresh full scan at `/tmp/darwin-full-current-map-kms-gns.json.gz` covered
42,009 paths, including 25,891 Lean sources and 246,254 lexical declaration
candidates. The Python dependency oracle analyzed 2,908 repo-owned scripts and
2,654 reference files. It found 91,566 Lean-source imports, 35,192 pinned
package imports, 1,508 Python imports, and 252 test-import edges. This scan is
not a stable whole-worktree generation: three unrelated files changed while it
ran. Compiler fingerprints remain unjoined because the available declaration
DAG metadata does not match the current source generation. These figures are
inventory evidence, not full semantic classification or proof status.

The KMS/GNS/attention pilot covers seven current Lean modules in
`/tmp/darwin-kms-gns-attention-map.json.gz`; their selected source paths were
stable during that scan. The resulting 14-task packet in
`/tmp/darwin-kms-gns-attention-review-v2.jsonl` binds source hashes and leaves
both `artifact_role` and `semantic_archetype` labels pending. Its schema v2
reports `explicit_path_selection`, stable selected paths, and a truncated
dependency context; it does not call this a whole-worktree taxonomy.
Legacy maps without an inventory-scope field are now reported as
`inventory_scope_unspecified_selected_sources_hash_verified`, with dependency
context scope explicitly unknown rather than misreported as an inconsistent
map.

The observed dependency chain distinguishes several candidate archetypes:
finite router Gibbs/softmax identities (`LLM.KMSSoftmaxBridge` and
`LLM.ScalarThermoBridge`), the finite diagonal attention state
(`QuantumContext.AttentionKMSState`), its existing quotient GNS wrapper
(`AttentionGNSBridge`), rowwise kernel-to-state correspondence
(`SoftmaxKMSMarkovBridge`), score-gauge invariance
(`AttentionGaugeGNSBridge`), and selected-stage modular flow
(`ColimitAttentionTomitaFlow`). They must remain separate semantic labels:
the rowwise softmax/Gibbs identities do not establish that a whole transformer
is a KMS system. `KMSSoftmaxBridge` and `ScalarThermoBridge` have multiple
Lake import-closure targets in the full map. Those targets are build-reachability
candidates, not exclusive ownership or maintainer attribution.

### Resumed stop approval and regression verification — 2026-10-30

On receipt of the repeated approval for diagnostic session 57100, that session
was no longer available. Host process inspection found no running Lean or Lake
process; no additional process was killed. The earlier interruption and locked
Lean verification are recorded above. The preserved diagnostic log remains at
`/tmp/darwin-yangmills-phase-diagnostic.log`.

Fresh serialized Sage regression checks passed 85 tests across batch export,
raw Arango ingestion, fossil-overlay ingestion, InfoTree DNA, taxonomy readiness,
and latent taxonomy. Two additional shared-context regressions then passed
in the five-test raw-ingestion suite: reconstructing reference-to-declaration
membership through context vertices preserves the legacy endpoint multiset for
both context kinds, including empty contexts; cross-root context-key reuse is
rejected. The layout-specific generation fingerprint differs from the legacy
fingerprint. These are fixture-based checks, not live Arango validation.

The shared-context storage layout remains pending integration: named-graph and
descent consumers must be checked for layout awareness, followed by real-capture
and live-database validation. No whole-repository pipeline completion, lossless
capture, or taxonomy accuracy claim follows from these regression results.

### Generation-aware named graph integration — 2026-10-30

`arango_raw_infotree_graph.py --generation-id ID` now reads a completed live
raw-generation receipt, validates its identity/layout collection map, and
constructs the appropriate expanded or shared-context graph definition.
All exported edge families are covered, including previously omitted goal,
free-variable, tactic-argument and message edges. Generation graphs default
to distinct names and disallow replacement. Existing graph definitions must
match the requested definitions before reuse; collection counts are queried
before Gharial creation so missing collections are not implicitly fabricated.
The NetworkX probe receives the generation's actual node collection.

Nine raw-ingest/graph tests passed under the shared lock. They cover both
layouts, endpoint collections, cross-generation map rejection, and
non-mutating rejection of mismatched existing graphs. Live graph creation and
layout-aware descent verification remain pending; no production completion
claim is made. The concurrent mathematical intake was integrated through
existing Peirce and matrix-colimit owners, with evidence recorded in
`docs/AI_STUDIO_OPERATOR_ARITHMETIC_SYNTHESIS.md`.

### Immutable-generation descent verifier — 2026-10-30

The existing descent verifier now accepts `--generation-id`, validates the
completed live receipt and expected-count coverage, and remaps raw collection
queries into that exact namespace. Shared-context checks verify one exact
membership edge per reference/declaration, root agreement, local-context size,
and endpoint closure for every edge family. Missing collections fail before
query execution; cross-generation edges are rejected. The unbound `ig_nodes`
join is explicitly reported as not checked rather than treated as current.

Sixteen offline ingestion/graph/descent tests passed under the shared lock.
A read-only live run against existing expanded CFSGPort generation
`e05e4a108bcdf1d692338b63` passed every selected structural check and count
comparison, with zero failures. Evidence:
`/tmp/darwin-cfsg-expanded-descent-v5.json`. No live shared-context generation
has yet been tested, and the tactic-state coverage report from legacy mode is
not part of generation-mode verification. The reported scope is raw structural
descent and endpoint closure, not full compiler losslessness or external
semantic classification.

### Shared-context live equivalence and measured storage — 2026-10-30

The CFSGPort MatrixInverseTranspose capture now has two completed immutable
layouts: expanded `e05e4a108bcdf1d692338b63` and shared
`4278689dd7083bd6cecc33ba`. Fresh live descent checks passed for both:
29 expanded checks and 34 shared checks, with no live count mismatches.
Evidence: `/tmp/darwin-cfsg-expanded-descent-v6.json` and
`/tmp/darwin-cfsg-shared-descent-v6.json`.

The existing descent verifier gained `--compare-expanded-generation OLD`,
used together with `--generation-id SHARED`. It requires completed receipts,
correct layout order, and matching nonempty build/source provenance. It
compares all 16 raw row collections bidirectionally, ignoring only Arango's
namespace/revision metadata, then compares sorted declaration endpoint
multisets per mctx/lctx reference. Duplicates are retained. Queries materialize
one reference's context rather than a global reference-by-declaration product.
This is a read-only equivalence check, not a database migration.

The live comparison passed all 34 checks. Receipt edge totals fell from
43,824 to 17,172 (26,652 fewer, 60.8% reduction), while preserving the raw rows
and context endpoint multisets. Evidence:
`/tmp/darwin-cfsg-layout-equivalence-v6.json`. These edge totals are receipt
counts corroborated by the separate fresh live count checks. This measures
edge documents, not bytes on disk or traversal latency.

Eleven descent tests passed under Sage Python and the shared build lock,
including four new cases covering successful comparison, mismatched provenance,
changed raw rows, and changed context membership. The comparison explicitly
requires separate generation-descent verification; it does not alone prove
all edge families are closed, compiler losslessness, or equality of every edge
payload. The source sample is the preserved capture, not a claim that the
entire contemporary checkout has been recompiled. Larger capture scaling,
whole-repo coverage, provenance-bound labels, and taxonomy evaluation remain
open. No historical repository clones were created and neither generation
was overwritten or removed.
