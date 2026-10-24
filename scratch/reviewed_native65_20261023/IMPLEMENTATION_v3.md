# Native reviewed65 v3 — minimal consolidation candidate

Only new `native_reviewed_v3.py` and this contract added. V1/v2 untouched.
No builds/tests or live/dependency changes. Parent A-A/QA required before promotion.

## Scope correction

Use the real native root and **normal intact Lake caches**, including Mathlib,
Architect and workspace configuration caches. No cold-build gate, receipt producer,
cache attestation, network-isolation prerequisite, `--no-cache`, `--rehash`, or
custom cache deletion. No claim of fresh/reproducible-cache certification or
hermeticity. No dependency repair, pin change, import stripping or new theorem.

Reuse existing BuildLock/fd, runtime process precheck, bootstrap path reporting,
version check, Lake command builder, public axiom generator/count parser and
context fingerprint helper. No copied source closure. Preserve original probe.

## Actual commands and acceptance

Under one BuildLock, all compiler children inherit its fd and are awaited:

1. Record root revision, manifest contents/config hashes, root/dependency status,
   source bytes, bootstrap path report, exact selected targets.
2. Native `lake env lean --version` must match root toolchain; record Lake version
   and native LEAN_PATH. No custom path substitution.
3. `lake build <all exact ordered65 targets>` using existing command builder.
4. Fresh `lake env lean <actual source>` for EACH exact command-only Audit module,
   even if its Lake build used cache. Retain stdout/stderr and exit status.
5. Fresh generated public-API combined audit; reconcile all numeric module counts
   and exact roles with existing parser. Fresh original PolarizedShearSpinAudit.
6. Reuse existing context fingerprint snapshots before/after audit/probe. Require
   stable source/config/dependency snapshot and command-source hashes at finish.

Exit/launch failures keep logs and a failed report. Runner supports/rejects kwargs
explicitly, supports text stdin, and waits on interruption without killing a
compiler or releasing the lock early. There is no parallel build path.

## Two honest statuses

`local_kernel_status=passed`: selected native build succeeded (possibly cached),
both command sources freshly elaborated, combined public axiom audit/count checks
and original probe succeeded, and recorded source/config/context remained stable.
This is local kernel evidence for the environment actually used, not a fresh
rebuild or assurance that every cached artifact was built from today's sources.

`clean_release_status=passed`: local checks passed AND recorded checkout status
was clean, manifest git revisions matched, checked nested gitlinks matched, and
bootstrap path provenance passed. It adds source/pin cleanliness, **not cache
provenance certification**. The local report may say passed while release says
failed; there is deliberately no single ambiguous global PASS.

`run_native(..., clean_release=False)` returns a local-only result if checks pass
on stable dirty sources. `clean_release=True` still performs the same genuine
checks, then raises if release status failed, preserving both result fields.
Use the latter for the eventual reviewed release CI job. A dirty Architect file
at the correct HEAD remains recorded and fails release. Atlas untracked/GIFT dirty
similarly fail release; missing configs/sources may also cause native Lake failure.
No preflight silently edits, cleans, fetches or repairs them. Native build itself
may produce ordinary generated artifacts; any recorded source/pin drift fails.

## Exact65 selection, optional mode, current56 integration

Literal EXPECTED_TARGETS is frozen from inspected upstream revision
`81867ee217620005c5c18c4cb78b15f8d24f68db`. Compare ordered tuple equality with the
native JSON; no length-only check, subset, silent append or fallback. The current
56-target file must receive the previously reviewed nine additions in the same
order before native65 can run. Parent promotion is separate; no change made here.

Promote v3 to `tools/quality/reviewed_native.py`. Add optional `--mode native` while
keeping copied mode default/compatible. Branch before copied Mathlib-root
resolution/closure/output creation. In native mode reject copied Mathlib/cache
arguments and call `run_native(repo, args.output, wait=args.wait_for_build_lock,
clean_release=args.clean_release)`. `--mathlib-root` stays required only in copied
mode. Ensure direct script invocation can import the root `tools` package.
CI opts into native plus `--clean-release`; developer local checking may omit it.
Never interpret local-only success as clean-release acceptance.

Output stays a fresh ignored `scratch/native_reviewed_runs/<run-name>` directory,
validated before creation; it cannot overlap configured dependencies or build
folders. No existing report reused. Invalid target intake fails without a report
because no safe run directory has yet been created.

## Source/context reporting limits

Paperproof uses checkout root for Git identity and `subDir=lean` package root for
native package identification. Manifest/config/source/status snapshots are taken
before and after work. Source inventory includes ignored files in dependency
checkout trees and root lean/tools/proofs, excluding .git/.lake/__pycache__ and
Python bytecode. Cached Lake configuration is intentionally allowed and excluded
from source stability. Root metadata is separately hashed. Symlink files record
link text/resolved bytes; source directory symlinks fail as unsupported inventory.

Nested gitlink checkout identity/status is recursively recorded for Git packages
and gitlink path dependencies. In-tree tracked path packages with nested gitlinks
are flagged unchecked and cannot obtain clean-release status; local checking can
still proceed. These observations do not certify all arbitrary inputs a custom
native build script could read. Context helper records actual queried olean inputs;
no recursive or hermetic artifact claim. No new infrastructure acceptance layer.

## Deferred review/QA, no execution here

Review exact65 argv and unchanged copied mode; local success vs dirty-release
failure; clean-release CLI nonzero while preserving local pass; real bootstrap
Atlas/GIFT and Architect status; normal warm caches left intact; Paperproof roots;
fd inheritance, interruption, launch/nonzero receipts and stdin; fresh two Audit
commands; malformed count rejection; original probe; source/config/context drift;
safe output rejection. Parent schedules any tests/builds serially after A-A/QA.
