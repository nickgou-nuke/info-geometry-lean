# Independent source review: nonaccepting CI diagnostics

Reviewer role: `/root/witt_born_author`, separate from candidate author.
Baseline repository revision: `0db6e19eadcfffbfc468138a25d88ff7bef326fb`.

## Decision

No blocking issue found in the final candidate at source-review scope. The
runner and workflow preserve strict acceptance and isolate diagnostic builds.
One requested isolation hardening was incorporated: reject a symlinked
diagnostic root, validate the workspace before creating outputs, and require
the resolved diagnostic library to remain inside the fresh run directory.

## Reviewed identities

| Candidate | SHA256 |
|---|---|
| `diagnose.py` | `46464783b6c273365688fd38bf19dd3dcd544cfbf9e60efe165922712f516ce7` |
| `zorn-witt-born.yml` | `91717dc7c280174c91f55a4c23c9925c5c5254861ba1e1da6ac01f3e3449a9b2` |
| `workflow-integration.patch` | `87b948161e85ea39f1b17bbde234cd37f54365d410a103a57ce4e31a074c58a3` |

## Invariants checked by reading the source

- Entry requires a full-suite strict receipt with `status: failed`,
  `audit_expected: true`, `audit_status: not-run`, matching targets, and a
  completed compiler command with positive nonzero return code. Missing,
  successful, audit-failed, interrupted, and infrastructure-only receipts
  therefore do not launch diagnostic compilation.
- The failed receipt must match the current pinned compiler binary,
  dependency revisions/search paths, manifest, verifier identity, source
  closure and hashes, and audit-source hash. Mutable input identities are
  checked again before and after compilation.
- Every run creates a new UUID directory. `LEAN_PATH` consists of that run's
  fresh library plus the verified native package libraries. The strict
  `compiled.json` and compiled `.olean` files are neither read nor written.
  The sole strict output read is `report.json`, used as diagnostic provenance
  and an entry guard.
- Compilation is sequential and holds the maintained exclusive build lock;
  a busy lock fails closed rather than creating a parallel compiler lane.
- `-DwarningAsError=false` is explicit. No linter is disabled. Diagnostic
  receipts override the inherited environment field to report this policy
  honestly.
- Only zero-return-code modules enter the `elaborated` state. A module is
  skipped if any repository dependency is not elaborated, which propagates
  real failures through all descendants while leaving independent branches
  available. A signalled diagnostic compiler aborts the run.
- The runner never compiles an audit file, writes a strict acceptance
  receipt, or populates a strict cache. Every report has `acceptance: false`
  and `audit_status: not-run-diagnostic-only`.
- Normal completion returns 2; guarded errors, busy locks, interruption,
  parser errors, and even `--help` exit nonzero.

## CI failure conditions

The full-scope strict step gains only an ID. Its command, warning policy,
pipefail behavior, and lack of `continue-on-error` are unchanged. Diagnostics
run only when `failure()` holds and that exact strict step's outcome is
`failure`. A setup or counterexample failure that skips the full-scope step
does not satisfy that condition.

The diagnostic shell also uses pipefail and has no `continue-on-error`.
Consequently diagnostics cannot turn the failed job green. The existing
strict audit-confirmation step remains unchanged. The existing always-on
evidence collection/upload remains in place; new collection copies only
diagnostic JSON/log files and the runner source, not diagnostic binaries.

A read-only `diff -u` of the complete YAML against the baseline confirmed
that its changes are confined to the path trigger, strict-step ID, diagnostic
step, and evidence collection. The supplied patch contains those changes.

## Validation limits

This review performed source reads, source comparison, and SHA256 reads only.
No Python execution, syntax-parser validation, compiler invocation, build,
test, local CI execution, or GitHub mutation was performed. No tracked
repository file was changed. Runtime validation remains with the parent and
the scoped CI workflow.
