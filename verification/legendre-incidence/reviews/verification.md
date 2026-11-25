# Independent focused-verification review

Date: 2026-11-24. Checkout HEAD at review: `5a79f362eccbac2def1cecfc1c76380f106365fa`.
Reviewer: `legendre_souriau_audit`.

This is a static review. I did not run Lean, Lake, the verification wrapper,
the audit program, or any command that acquires or alters the build lock.
The parent reports that its first focused run is queued behind another task.
This report does not turn that queue entry into a compiler result.

## Result

The focused Lake configuration is consistent with the declared scope and the
root dependency pins. Native `--packages` is an appropriate way to reuse the
existing exact source checkouts; it does not require a tracked manifest edit
or a linked Lake directory. Normal dependency artifact writes must remain
enabled under the shared lock.

The original wrapper needs stronger input and runtime provenance before its
success should be presented as a reusable, self-contained validation
certificate. The isolated candidate `check_hardened.py` in this directory
addresses the concrete issues below. It is ready for independent review and
promotion to `verification/legendre-incidence/check.py`; I have not executed
it. Its Python syntax was checked with `ast.parse`, exit 0.

## What was checked

- `verification/legendre-incidence/check.py`, `audit.py`, `README.md`,
  `lakefile.toml`, `lean-toolchain`, and `lake-manifest.json`.
- `.github/workflows/legendre-incidence.yml` and the current four mathematical
  owners plus `Twistor/LegendreIncidenceAudit.lean` for declaration shapes and
  target scope.
- `docs/LEGENDRE_INCIDENCE_OPERATOR_AUDIT_20261124.md`, including the newly
  expanded completed-connections and validation sections.
- The repository's `AGENTS.md`, verification/runbook instructions,
  `WARNING_DO_NOT_RUN_CACHE.md`, and the actual shared-lock, interruption, and
  Lake-workspace integrity helpers.
- The recovered Lean 4.34.1 Lake source, specifically dependency materialization,
  `--packages`, automatic package overrides, runtime environment construction,
  `self-check`, and `env` process launching. These were source reads only.

## Correct configuration and acceptance boundaries

1. The focused toolchain is byte-identical to the root specification,
   `leanprover/lean4:v4.34.1`.
2. All nine focused Git dependency triples `(URL, revision, subdirectory)`
   equal their root counterparts. Mathlib is pinned to
   `d13f23b723b8a846827a245b89c10fc7d3f11612`. The other eight packages are
   plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq,
   batteries, and Cli. I independently compared the manifests by reading JSON.
3. The focused source directory is `../../lean`; the four owners and their
   audit are canonical source files, not copied proof variants. The five
   explicit default targets do not claim a whole-repository build.
4. With native Lake defaults, project artifacts belong to the focused
   package's `.lake/build`. Explicitly selected dependency checkouts may
   receive normal generated artifacts in their own build directories. This
   distinction is already stated correctly in the README.
5. The added CI uses `set -euo pipefail` around compilation and a separate
   fresh axiom-printing invocation. The axiom validator compares the reported
   declaration names with the expected inventory and rejects every axiom
   outside `propext`, `Classical.choice`, and `Quot.sound`. A successful source
   inventory scan alone does not establish this axiom result.

## Concrete wrapper findings and candidate changes

| Finding in original wrapper | Consequence | Candidate treatment |
|---|---|---|
| Toolchain files agree, but the selected `--lake` executable is not checked. | A file pin alone does not record which runtime performed elaboration. The parent's separate observed runtime check supports the current attempt, but the reusable wrapper lacks that enforcement. | Checks Lake's embedded Lean release, runs native `lake self-check` to compare actual Lean/Lake Git revisions, reads only the needed runtime paths from a configuration-free `lake env` probe, checks a common actual runtime prefix, checks Lean's own version/prefix, and records binary hashes. |
| Pins are read before a possibly long lock wait. | The earlier package list can become stale while the process waits. | Re-runs all pin and workspace checks after acquiring the lock and uses that package list for the command. |
| No source/configuration stability comparison spans the build. | A successful command and a later source tree are not automatically the same input. | Hashes the four owners, audit, recursive repository import closure, selected additional repository sources, control files, and existing dependency configurations before and after. Generated `.lake` outputs are outside this inventory. |
| Dependency checks validate only the leaf directory, HEAD, and tracked cleanliness. | A dependency could itself be a linked Git worktree or use a symlinked Lake root even though its leaf is an ordinary directory. Resolving the supplied root first also hides a symlink. | Checks lexical dependency paths before resolution and applies the maintained workspace-integrity helper to each actual package checkout. Also requires it to be its own Git root. |
| Native automatic package overrides are not considered. | Lake loads `.lake/package-overrides.json` before CLI overrides. The explicit nine-entry CLI override wins for those nine names, but default mode could consume a local override that the original pin checks never inspected. | Rejects such local override files in the project, focused package, and dependency workspaces before and after. At review time neither root nor focused override file existed. |
| Tracked-clean status ignores untracked Lean/config files. | The source revision alone need not describe all build-relevant files. | Rejects untracked Lean/config source files while excluding normal `.lake` and `artifacts` outputs. It still allows ordinary generated caches. |
| The compiler process does not inherit the lock descriptor. | If the wrapper dies while its separately grouped child survives, the wrapper's descriptor can close before the child exits. Ctrl-C handling itself was already careful. | Uses the existing `BuildLock.fileno()` API and `pass_fds`, retaining the maintained interruption/wait helper. No build timeout or automatic kill policy is introduced. |

The candidate keeps legitimate Elan shim invocation intact: it does **not**
resolve the selected `.../bin/lake` executable name to `elan` before invoking
it. It checks the native runtime paths that Lake itself reports instead.

Cold-cache default mode may let native Lake materialize missing pinned
dependencies. Existing packages are checked before the command, and every
package must be present and match its pin after a successful workspace
command. An explicitly selected shared dependency root still requires all
nine source checkouts up front. No source restoration, cleanup, chmod,
manifest mutation, or cache deletion is added.

The runtime environment probe can contain optional cache credentials. The
candidate captures that output privately, selects only runtime identity
fields, and does not echo full environment output, including on failure.

## Remaining bounded implementation considerations

- The import-closure scanner is a source-provenance helper, not a Lean
  parser or a replacement for Lake dependency resolution. It handles the
  ordinary and public/private/meta import forms present in these owners.
  New unsupported import syntax should extend that scanner. The actual
  compiler and transitive axiom audit remain the acceptance gates.
- The declaration scanner in `audit.py` covers the declaration forms now
  present: one explicit namespace per owner and ordinary named definitions,
  abbreviations, theorems, and lemmas. It should reject or explicitly support
  newly introduced `protected`, `opaque`, `instance`, `class`, or nested
  namespace forms before claiming complete future coverage. No current
  declaration omission of that kind was found.
- `audit.py` compares a set of names, so duplicate axiom records are not
  rejected. Requiring each expected name exactly once would make mixed or
  concatenated logs easier to detect. The current CI fresh invocation and
  `pipefail` already exclude a failed command being accepted just because
  an old log exists.
- An arbitrary supplied `--log` file is not by itself tied to current source
  hashes. The publication record should preserve the fresh command's exit
  result, source snapshot identity, runtime identity, and its associated
  log together. The new wrapper emits the input digest and runtime identity;
  the final publication record can bind those to the axiom log.
- This is a controlled validation runner, not an adversarial command sandbox.
  Its documented commands are build, cache hydration, and `env lean`. The
  original generic Lake-argument interface is retained; callers must not
  use it to request configuration replacement, dependency updates, or
  destructive cleaning forbidden by repository policy.

## Documentation status review

The parent updated the report during this review. The current report now
correctly separates the original main-source baseline from four new owners,
moves the graph/Grassmannian/cotangent links into completed source contracts,
describes the moving grading and explicit reference transvection, and keeps
the exact remaining global/physical boundaries.

The former claim that a runtime is unavailable has been replaced by a
historical account of exits 126/127 and an explicit current queued-build
status. That is the correct status until an actual result is observed.

Before publication, replace only that current status paragraph with the
observed build and fresh axiom results: checked revision/source identities,
runtime identity, all selected targets, exact commands, exit codes, and
declaration/axiom counts. Preserve the old failed attempts as historical
environment evidence if useful; they are not Lean counterexamples. Do not
claim a full repository certificate, an integrated flow, global
para-Kähler/supermanifold construction, physical supersymmetry, or a
fixed-Zorn-cut intertwiner from the focused results.

## Review fingerprints

Original reviewed `check.py` SHA-256:
`d88f926e33704e1feebe548a355f43c1745c0215b5c14124949f431255918530`.

Candidate `check_hardened.py` SHA-256 after syntax validation:
`43a5b92785c2560e458c3e2a1765860262499c54597ba75d364c03de4215dcf1`.

Focused Lake configuration SHA-256:
`d0b38869afeb6ab17fa9374e7c775b1de579cdb7dd368a2f2500d16b1d74e16c`.

Focused manifest SHA-256:
`997e49b4df3bb3daa8261590cc1b17db85084efefdef6a1d05c76caf3d549745`.

These fingerprints identify this review point; integration or compiler-driven
repairs require their own final validation record.

## Follow-up review: integrated wrapper, unique audit records, and README

I independently compared the promoted wrapper with `check_hardened.py`. The
only difference is removal of the candidate-installation sentence from the
docstring; there is no executable-code difference.

The small `audit.py` delta correctly imports `Counter`, counts the declaration
name in every parsed axiom record, and rejects every name with a count other
than one in addition to the existing missing-name, unexpected-name, and
unapproved-axiom checks. Thus a duplicate record, including an identical
duplicate, cannot silently collapse into the accepted name set. A missing
record remains rejected by set inequality. An unapproved axiom in any record
remains rejected by the union of reported axioms. This resolves the duplicate
record finding above without changing the source declaration inventory.

The revised README accurately states Python 3.11/POSIX requirements, actual
runtime checks, checks after acquiring the lock, source/configuration
stability checks, normal writable dependency caches, and the bounded scope of
the declaration scanner. It now expressly requires a successful Lean exit
before accepting a supplied axiom log and distinguishes focused closure
validation from whole-repository certification.

One small presentation improvement remains optional: add `set -euo pipefail`
to the reproducible shell block, or join the fresh Lean invocation and log
validator with `&&`, so copying the block as a script automatically enforces
the successful-exit requirement already stated in prose and implemented in
the workflow. This is not a defect in the new Counter check.

Disposition: the reviewed integration and duplicate-record delta are
accepted at static-review scope. No additional code was generated or changed
and no runtime test, Lean/Lake command, or lock operation was performed for
this follow-up.
