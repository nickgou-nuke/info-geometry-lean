# Promoted V3 QA — prepared, not executed

Targets: `tools/quality/reviewed_native.py`, `tools/quality/check_reviewed_prs.py`,
`tools/quality/reviewed_prs_20260921.json`. James A-A passed per parent; execution
still waits for Ampere's aggregate terminal result. Rebaseline all three at run
start; workflow is being handled separately and must not silently join the freeze.

Prepared fixtures in `test_native_live.py` replace the old cold-cache candidate
fixtures. They use temporary directories and mocks, do not invoke Lake, and never
edit owners or dependencies. Mocked `local_kernel_status=passed` / clean-release
states establish control flow only, not actual native acceptance.

Coverage: actual ignored-source byte hashing; symlink file binding and directory
rejection; intact `.lake/config` cache preservation; materialized Paperproof-style
`subDir=lean`; missing config/directory and wrong revision preflight rejection;
exact ordered65 specification; safe output shape/traversal/existing/ignored guards;
local-vs-clean-release distinction; exact native build argv and fresh command-only
reruns; failure/launch logs; runner supported/unknown kwargs; propagated lock fd
at mocked Popen sites; optional CLI dispatch and bad/default flag behavior.

After Ampere terminal, one shared-lock host-prechecked job should:

1. Record baseline hashes, command/tool versions and actual session handle.
2. Run this sandbox fixture file and the existing audit-generator regressions
   serially; record exact counts, skips and logs. No full 65 build.
3. Run direct-script/package CLI help/import smoke checks; assertions of CLI
   native failures use mocks, without opening the real native build lane twice.
4. Supplement with a tiny real Python child using the held lock descriptor and
   `fstat`; for the nested V3 runner use mocked context hooks unless an isolated
   fixture run is explicitly authorized. Never wrap actual run_native in a second
   acquisition of the same nonreentrant shared lock.
5. Inspect current real materialization/provenance read-only if authorized;
   distinguish Atlas/GIFT/Architect findings from the earlier source-only policy.
   Wrong revision or missing config must prevent Lake before package repair/fetch;
   dirty pinned sources may support local-only checks, never clean release.
6. Check final three hashes; preserve the preceding failed aggregate build as
   separate debt. No release/full-native acceptance from these unit/mock tests.

Pending coverage to extend after execution feedback: snapshot git/subDir identity
using fresh local Git repos; nested gitlinks; before/after context/source drift;
interrupt-resume/no-kill behavior; output ancestor symlinks and provider overlap;
actual final workflow selection. Do not reinstate cold-cache or hermetic/offline
claims. The real 65-target build remains unrun by this QA task.
