# Independent scoped CI source review

Reviewed candidate and integrated owner:
`witt-born-candidates/ci/zorn-witt-born.yml` and
`.github/workflows/zorn-witt-born.yml`.

Integrated workflow SHA-256 at final review:
`e746f31072307210f33b722d41b95ebbc77de51a6749c48cc5e4f551593c4d32`.

The final owner is byte-identical to the initially reviewed candidate.
Optional event-name and PR head/base provenance fields were briefly proposed
and source-reviewed, then removed before publication because their separate
syntax recheck was blocked by another task's shared build lock. The final
source retains the original exact event SHA, checked-out revision/tree, and
run identifiers. No lock or other task's process was altered.

This reviewer read the complete workflow, the maintained checker and lock,
root and pinned Mathlib manifests, the cache CLI's module-argument contract,
and repository CI/cache policy. Read-only source inventories checked native
dependency pins and trigger coverage. No compiler, build, syntax test,
workflow execution, cache retrieval, or axiom audit was run by this reviewer.

## Source identity and event scope

The workflow creates an ordinary independent checkout, fetches `GITHUB_SHA`,
checks the detached checkout equals that SHA, and records its revision and
tree before dependency preparation. It performs no submodule checkout and
passes no GitHub credential to Git.

For a `pull_request` event, `GITHUB_SHA` identifies the merge-test revision.
For manual dispatch it identifies the selected event revision. A result must
therefore be reported against the recorded SHA/tree; it is not automatically
a certificate for a distinct pull-request head SHA.

The final workflow does not record separate event-name or PR head/base fields.
Its exact event SHA, checked-out revision/tree, and run identifiers identify
the tested source. The merge-test distinction above remains part of the
interpretation of any resulting CI receipt.

## Pin preservation and dependency layout

The Lean version is read from the checked-out `lean-toolchain`, then verified
by the native checker. The Mathlib checkout uses the exact root manifest
revision and is checked for revision equality, clean tracked source, ordinary
Git metadata, and matching toolchain.

The pinned Mathlib manifest has exactly the eight names expected by the
workflow: `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`,
`aesop`, `Qq`, `batteries`, and `Cli`. Read-only comparison confirmed that
every one has the same URL and revision in the root manifest, has Git type,
and has no subdirectory selection. Its packages directory is `.lake/packages`.

Cache retrieval occurs in that fresh Mathlib checkout and selects the direct
native imports of the actual full source closure. The pinned cache CLI accepts
module names and includes their imported dependencies. Root Lake configuration
and optional root packages are not materialized by this command.

After retrieval, the workflow moves only newly created job-owned dependency
directories to a flat layout. It preserves each directory's Git metadata and
artifacts, verifies its revision and tracked cleanliness before and after,
rejects pre-existing destinations and symlinked checkout roots, and does not
delete or clean existing caches. Native compilation thereafter uses explicit
search paths and does not need the moved Mathlib Lake layout to remain active.

Both root and native manifests are hashed before cache preparation and checked
afterward. The checker separately records and verifies compiler binary,
dependency revisions, manifest, verifier, source, and audit identities.

## Serialization and failures

Cache preparation uses one directly constructed maintained exclusive
`BuildLock`, passing its descriptor into the spawned command. Both native
suites use the maintained checker and its exclusive lock. The steps execute
sequentially, and concurrency configuration does not cancel an in-progress
run merely because a newer PR revision arrives.

Shell pipelines use `set -euo pipefail`, preserving nonzero Python/checker
results through `tee`. The final success check requires `compiled`,
`audit_expected`, and `audit_status=passed` for both suites, then rechecks
their source hashes. It cannot turn a partial compile or a skipped audit into
success.

Receipts, logs, audit source, and checker source are collected with `always()`
after ordinary step failures and uploaded as a run-specific artifact.
This is a prospective source review of those mechanisms, not evidence that
an artifact or CI result currently exists.

## Trigger and acceptance scope

Independent import inventory found 50 repository source files in the current
full-suite closure. Every one appears in the pull-request path filter. The
workflow also triggers for changes to the selected audit/checker sources,
maintained lock/imported Python helpers, pins, aggregate import, and itself.

The light suite checks only supplied-table counterexamples. The full suite
checks the selected real Zorn, Souriau, Klein, Witt/Born, and counterexample
closure and its 15 selected audit owners. The workflow neither invokes nor
claims to replace every root Lake target, the maintained staged proof gate,
or the maintained push gate.

The workflow requests only `contents: read`, contains no secret interpolation,
does not dump the environment, and does not introduce pin edits, unsafe
proof flags, cache-deletion commands, or continued-success failure bypasses.

## Disposition

No blocking source-level defect was found in the reviewed candidate.
Integration and syntax checks are root-owned. Actual GitHub execution,
native elaboration, declaration auditing, and their exact outcomes remain
required before reporting a successful CI result.
