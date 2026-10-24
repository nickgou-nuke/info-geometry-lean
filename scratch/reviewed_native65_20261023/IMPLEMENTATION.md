# Optional native reviewed65 — candidate, not acceptance evidence

Candidate: `native_reviewed.py`; no builds/tests/import execution performed.
No live checker, workflow, source owner, dependency, manifest or pin changed.
Parent A-A/QA and subsequent serialized tests are required before promotion.

## Grounding and reuse

The current `tools/quality/check_reviewed_prs.py` closure resolver only admits
Mathlib/Lean/Std/Init external imports and copies repository closure into a
separate source/lib tree, configuring LEAN_PATH from Mathlib. Native mode must
branch BEFORE that resolver; adding Architect to its whitelist is insufficient.
The live `tools/quality/reviewed_audit_source.py` already implements public
`Lean.collectAxioms`, numeric owner counts, exact two command-only roles, source
hash guards, and `parse_audit_output`. Reuse it unchanged.

Candidate imports, rather than reimplements:

- `tools.build_lock.BuildLock` and `fileno()` for the one shared compiler lane.
- `tools.infra.check_runtime_acceptance.idle` and `require`; subprocess waiting
  follows its interrupt-safe pattern, preserving the lock until child termination.
- `tools.infra.ci_bootstrap.path_package_report`, path containment and version checks.
- `tools.infra.build.lake_build_command` for all 65 exact root targets.
- `tools.infra.pantograph_environment.build_lean_context_manifest` and SHA helper
  for actual Lean dependency-query olean hashes, config hashes, source and toolchain
  evidence. This helper is a context snapshot, NOT an authenticated cache receipt.
- Existing reviewed audit generator/parser/role mapping and existing
  `proofs/PolarizedShearSpinAudit.lean` source, without replacement witnesses.

Bounded search of tools for dependency revision/dirty/provenance handling found
bootstrap covers direct path packages, not all manifest git packages. The added
small `source_identity` check supplies exact installed git HEAD/clean status,
config presence and supported provider layout checks. It rejects unknown types,
subDir layouts and nested gitlinks instead of guessing transitive provenance.
Root manifest is the Lake-resolved package set; all entries, inherited included,
are checked, not just Mathlib or imports selected by a text scanner.

## Optional integration (not applied)

Promote candidate as `tools/quality/reviewed_native.py`; normal package imports
require the repository root on sys.path for direct checker invocation.
Add `--mode {copied,native}` default `copied`, and `--wait-for-build-lock`.
Make `--mathlib-root` syntactically optional but required in copied mode.
Immediately after argument parsing/root determination, BEFORE `.resolve()` of
mathlib-root, output creation, old closure or old flock:

```python
if args.mode == 'native':
    if args.mathlib_root is not None or args.cache_dir is not None:
        parser.error('native mode uses root Lake; copied-cache/mathlib overrides are invalid')
    from tools.quality.reviewed_native import run_native
    run_native(repo, args.output, wait=args.wait_for_build_lock)
    return
if args.mathlib_root is None:
    parser.error('--mathlib-root is required for copied mode')
# existing copied implementation continues unchanged
```

Use the full native checkout with all recorded path/git sources provisioned at
exact existing identities; sparse copied-lane checkout is insufficient. Workflow
invocation is `python3 tools/quality/check_reviewed_prs.py --mode native --output
scratch/<unique-ignored-run-dir> --wait-for-build-lock` from repository root.
Upload output artifacts even on failure. Keep copied mode available; do not
silently fall back to it when native mode fails. Native job must not run alongside
another compiler/test process. No live workflow is proposed changed here.

## Acceptance flow and provenance boundary

1. Load entire existing JSON selection, validate names/roles and require exactly
   65 entries. No hard-coded reduced target subset. Role dependency owners remain.
2. Fresh ignored output; one BuildLock covering preflight through final snapshots.
   Every compiler subprocess inherits its fd and is waited synchronously. On
   Ctrl-C wait without killing; failure is recorded before releasing the lock.
3. Bootstrap path preflight and clean pinned git-package checks run BEFORE Lake.
   Preserve a failed report with explicit cause. Parent reports Atlas untracked,
   GIFT dirty and Architect at correct 54d3... HEAD but dirty Command.lean. Atlas/
   GIFT fail bootstrap immediately; after their resolution Architect still fails
   git cleanliness. No dirty package gets accepted merely because HEAD matches.
4. Initial implementation requires cold native package/root build dirs and no
   cached Lake configuration. It never deletes or cleans anything. Run in a fresh
   CI checkout with exact provisioned dependency sources. This deliberately
   refuses the current shared development caches: a hash alone cannot authenticate
   oleans built while dependency source was dirty. Cached native mode requires a
   separate reviewed receipt binding source/config/toolchain and artifact hashes;
   no such receipt is fabricated here. This is a material cost/limitation.
5. All Lake calls run from actual root and are given `--offline --no-cache`;
   build additionally uses `--rehash`. These options were read in pinned Lake
   `Lake/CLI/Main.lean`. No lake update, moving refs, alternate lakefile, copied
   Mathlib closure, source stub or import removal. Offline missing dependency
   failure is surfaced, not repaired. Native package configs execute normally;
   provisioning and any native binary/toolchain requirements remain explicit.
6. Build the full selection through native root Lake. Freshly elaborate both
   command-only source files via `lake env lean` even if Lake just built them.
   Record command argv, cwd, terminal exit, stdout/stderr separately. Combined
   generated audit and the original proof probe also execute fresh, preserving
   public collector and count parser requirements. No theorem is introduced.
7. Reuse actual dependency context snapshots before/after audit/probe, reject
   outside-project/toolchain paths and unexpected project library providers.
   Selected declarations are audited in the resulting environment; dependency
   axioms are traversed by the public API, not by a Python namespace approximation.
8. Require stable root tracked-file hashes, root revision, manifest/config and
   all dependency identities/cleanliness before success. Dependencies may write
   ignored build outputs, not source/pins. Recheck command-source hashes. A source
   drift or context drift fails. Reports start failed and become passed only at
   the terminal acceptance point.

The context helper fingerprints the olean inputs reported by Lean's dependency
query for audit/probe; it is not advertised as recursive enumeration of every
artifact. Transitive dependency source authority here comes from clean exact
manifest checkouts and a cold native build, not that helper alone. This candidate
assumes the installed pinned Lean toolchain and committed build configuration
are trusted CI inputs. Ambient Lean/Lake path overrides are rejected.

## Parent review and deferred tests

No tests/builds run here. Before promotion, review unsupported package layouts
and cold configuration-cache locations against actual pinned Lake installation;
reject unsupported layouts rather than loosening provenance checks. Offline mode
may surface missing native prerequisites that previously went unseen. No blanket
claim of successful clean-pin Architect compatibility is made.

Focused mocked Python contracts: all 65 argv entries retained; invalid selection;
Atlas/GIFT bootstrap failure before any Lake call; correct-HEAD dirty Architect
failure; wrong HEAD/missing config/provider; path traversal/symlink escape;
preexisting unproven build artifacts; fd propagation; interrupted child wait;
nonzero exit log/report; no fallback to copied mode; unchanged copied CLI behavior;
source/context drift; malformed/missing/duplicate numeric audit markers; exact
command-only modules each freshly elaborated once after native build.

Then parent runs locked real-native clean-source checks: all65 build, two fresh
command sources, combined public axiom audit/count reconciliation and original
probe. Require clean-pin Architect compatibility with root 4.34.1. Its declared
4.28-era dependency requirements do not authorize updating root pins or using
local dirty patches. Separate approval is needed for any dependency repair.
