# Candidate: isolated, nonaccepting native diagnostics

This candidate is conditional on another observed strict source-compilation
failure. It is not integrated into the repository and has not been executed,
syntax-tested, compiled, or used to produce a passing result.

## Intended installation

- `diagnose.py` becomes `verification/witt-born-null-exactness/diagnose.py`.
- `workflow-integration.patch` describes only the optional CI wiring.
- `zorn-witt-born.yml` is the complete resulting workflow candidate.

Source hashes at author freeze:

| File | SHA-256 |
| --- | --- |
| `diagnose.py` | `46464783b6c273365688fd38bf19dd3dcd544cfbf9e60efe165922712f516ce7` |
| `zorn-witt-born.yml` | `91717dc7c280174c91f55a4c23c9925c5c5254861ba1e1da6ac01f3e3449a9b2` |

The strict checker, proof owners, mathematical formulas, dependency pins,
audit code, staged gate, and push gate are unchanged.

## Why a separate diagnostic route can be useful

A strict owner compile turns unused simplifier arguments into fatal errors.
Stopping at the first such owner can require a complete CI cycle for each
later file. A separate run can retain all ordinary linter warnings while
continuing to elaborate independent modules, exposing later real errors in
the same source snapshot. It must not provide an alternate acceptance route.

Activate this candidate only if the next actual strict result warrants that
additional work. A passing strict run requires no diagnostic run.

## Entry guards

The script requires the current full-suite receipt to identify:

1. The exact full `witt-born-null-exactness` target set, with `status=failed`.
2. An expected strict audit that has not run because compilation failed.
3. A completed compiler command with positive nonzero return code. Signal
   termination is rejected rather than provoking another resource-intensive
   compilation pass.
4. The same pinned compiler binary, native dependency revisions/search paths,
   manifest, strict checker, and compiler-thread configuration.
5. Exactly the same ordered source closure and source hashes, and unchanged
   strict audit source.

The maintained workspace-integrity check runs before output creation. A
symlinked diagnostic root is rejected. Inputs are checked again under the
exclusive shared build lock and at the end of the run. The strict receipt's
byte hash and run ID are included in the diagnostic receipt.

## Isolation invariants

Each run gets a new UUID directory beneath `.lake/witt-born-diagnostics`.
Its resolved Lean library must remain inside that fresh directory.
`LEAN_PATH` contains only that diagnostic library plus the same pinned native
package artifact paths. Neither strict suite's repository `.olean` directory
is read or written. No `compiled.json` is loaded, created, or reused.

The script reuses the existing checker only for environment validation,
source/import inventory, receipt formatting, and child execution/cleanup.
The shared lock is constructed directly, acquired exclusively, and inherited
by each child. A busy lock produces a blocked diagnostic result; the script
does not wait, clear the lock, or signal another process.

All source modules use `lean -j1`. Only this isolated diagnostic invocation
passes `-DwarningAsError=false`; no linter is disabled and the strict checker
continues to pass `-DwarningAsError=true` for its owned modules.

The reported environment overrides `owned_warning_as_error` to `false` so it
cannot be mistaken for the strict checker's policy fingerprint.

## Failure collection

The script follows the same topological source closure. A successful child
is labeled `elaborated`, which is explicitly not a proof-acceptance status.
An ordinary Lean error is recorded, and independent modules continue.
Every module whose repository dependency failed or was skipped is skipped
with its blocking dependency names; this propagates through descendants.
Signal termination stops the diagnostic run immediately.

All diagnostics and return codes are retained. Compiler warnings remain
visible. No axiom audit is performed, so diagnostic outputs may not be used
as audited or accepted proof artifacts.

## Nonacceptance invariants

The receipt always has `acceptance: false` and
`audit_status: not-run-diagnostic-only`. Its top-level statuses are diagnostic
statuses; it never reports `compiled` or audit `passed`.

Completed diagnostics return exit code 2. Blocked/error/interrupted runs also
return nonzero. Even the argument parser's help exit is nonzero, making the
script unsuitable as a passing check under any invocation.

The CI step is conditional on `failure()` and the exact strict full-scope
step's outcome being `failure`. Bootstrap failure or counterexample failure
alone does not trigger it. No strict step gains `continue-on-error`.
If strict validation passes, diagnostics are skipped and the existing strict
receipt-confirmation step runs as before. If it fails, the job remains failed.

The existing always-run evidence collection is extended to retain diagnostic
JSON/log files and the diagnostic script, excluding its `.olean` outputs.

## Validation debt

This is an authored source candidate with an independent reviewer assigned.
No parser, test, compiler, build, workflow, or axiom audit was run by the
author. The root decides whether observed CI evidence justifies integration,
then owns source review and serialized validation.
