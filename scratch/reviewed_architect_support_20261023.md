# Full reviewed union with pinned Architect: design and test contracts

Status: DESIGN ONLY; no builds, tests, dependency changes, or CI-pass claim.
All nine October targets remain required. This supersedes the earlier proposal
to defer MajoranaCoefficientAction from the target list. Parent handles the
Grassmann URL-only restoration separately.

## Inspected source and concrete blocker

- `tools/quality/reviewed_prs_20260921.json`: 56 existing targets. Upstream
  `fix/main-verification-bootstrap-20261023` at
  `81867ee217620005c5c18c4cb78b15f8d24f68db` appends nine, preserving order and
  giving 65 unique targets. No target may be silently removed or skipped.
- `tools/quality/check_reviewed_prs.py`: `closure` resolves repository sources,
  treats Mathlib specially, and rejects other unresolved packages. Its present
  line-based parser is not a complete Lean import parser. The new dependency
  path includes MajoranaCoefficientAction → KitaevChainMajoranaZeroModes →
  MajoranaKitaevSpinorBridge → BulkBoundaryRegularizationBridge →
  KK.KasparovCycle → AnalyticalIndexCore → BottDirac → SpectralInference →
  Convex.HessianGeometry → Canonical.Triality → Architect.
- `lean/InfoGeometry/Canonical/Triality.lean` really imports Architect and uses
  its `@[blueprint ...]` attribute. Removing that import or replacing the
  attribute with an inert stub is not acceptable dependency support.
- Root `lakefile.lean` and `lake-manifest.json` require LeanArchitect from
  `https://github.com/hanwenzhu/LeanArchitect.git`, exact revision
  `54d3fb249685db8e5a564e0b3f331cff77991607`. Root Lean is 4.34.1.
- The inspected local package HEAD matches that revision, but Git reports
  ` M Architect/Command.lean`. The diff changes `exportEntriesFnEx?` from
  `fun _ _ es level => ...` to a record-valued callback with `exported`,
  `server`, and `private` fields. This is evidence of a local API adaptation,
  not evidence of clean-pin compatibility. Do not certify local dirty oleans
  as artifacts built from the manifest revision.
- The package's pinned `lean-toolchain` declares 4.28.0. Its lakefile requests
  batteries and Cli at v4.28.0. Its own manifest records batteries
  `495c008c3e3f4fb4256ff5582ddb3abf3198026f` and Cli
  `4f10f47646cb7d5748d6f423f4a07f98f7bbcc9e`.
- The root manifest instead selects batteries
  `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` and Cli
  `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204`, matching the inspected pinned
  Mathlib manifest. Root Mathlib is
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Architect's library entrypoint imports Attribute, Basic, CollectUsed,
  Command, Content, Load, Output, and Tactic. Their direct external imports are
  Lean and Batteries.Lean.NameMapAttribute. Cli is a declared package dependency,
  even though it was not found among those library-module imports. Do not
  confuse the module import closure with the package-resolution graph.

## Recommended lane: native root Lake environment

Replace the copied-Mathlib closure execution path for this lane with the
actual root Lake environment. Preserve the 65-target selection, combined
declaration audit, and existing PolarizedShearSpinAudit proof probe. This is
a scoped build of the reviewed union, not an all-default-targets build.

1. Use a fresh checkout of the exact repository revision, with its complete
   tracked package/configuration sources. The current sparse checkout is not
   sufficient for arbitrary native path packages. Do not borrow dependency
   directories or oleans from the shared dirty development checkout.
2. Provision only the dependency sources identified by the existing root
   manifest, without `lake update`, branch resolution, or metadata rewrites.
   An absent path dependency must have an approved reproducible source; do not
   infer a URL/revision from a directory name. Existing Atlas/GIFT provenance
   blockers remain blockers. InfoGeometryCore is now tracked source, not an
   initialized gitlink requirement.
3. Run native `ci_bootstrap` version/path preflight and a separate exact Git
   package provenance check. `ci_bootstrap paths` only checks direct path
   packages: it does not establish cleanliness of LeanArchitect or Mathlib.
4. Under the shared BuildLock, after compiler/test process precheck, establish
   clean exact-pin Architect compatibility by invoking its actual library
   target from the root package (`lake build Architect`, subject to verifying
   target resolution in implementation). Use root Lean 4.34.1 and root resolved
   batteries/Cli revisions. Do not run Lake from the dependency directory and
   thereby select its 4.28 toolchain/manifest. Do not build its unrelated
   blueprint executables or run blueprint conversion scripts.
5. This compatibility check must compile from a fresh isolated artifact area
   with no restored Architect output. Never delete the shared build cache to
   obtain this condition. A matching package HEAD plus an existing olean is
   insufficient. Save the compiler diagnostics and resolved package inventory.
6. Build every selected reviewed module natively, then elaborate the combined
   audit and proof probe through `lake env lean` in that same root environment.
   Preserve source imports and attributes byte-for-byte. Do not construct a
   substitute LEAN_PATH or add the shared package's build directory to it.
7. Final source/provenance recheck precedes publication of a successful report
   or cache. There is no success-with-deferred-target mode.

Use `tools.build_lock.BuildLock` for a transaction spanning these sequential
steps, with child descriptor retention and process prechecks. Reuse the native
build command constructor if the orchestrator already owns the lock; do not
call a second lock-acquiring wrapper inside it. Alternatively use the existing
locked build wrapper for a standalone phase, with a new guarded audit phase
and source stability checks across both. Never start parallel compilers or
kill an unrelated build. A shared build lock does not prevent source edits.

## Exact-pin compatibility is a separate acceptance condition

The package's historical toolchain string need not equal the root's string to
permit a compatibility experiment; that mismatch must be recorded, not silently
edited. Actual acceptance requires the unmodified 54d3… source to compile under
the root 4.34.1 environment and the preserved native imports to elaborate.

If that clean experiment fails, report `blocked_clean_pinned_dependency` with
its diagnostics and retain all 65 required targets as incomplete. Do not copy
the local Command.lean patch, use dirty outputs, downgrade root Lean, follow a
moving branch, or reclassify Architect as a trusted builtin to obtain green.
Dependency source patches, an overlay carrying such a patch, or any dependency
pin update require separate explicit approval and provenance review. None is
included in this design. Under the present constraints there may be no passing
execution until that separate decision; this is not permission to reduce scope.

## Closure and source fingerprint contract

The Lake-resolved package graph is authoritative for dependency selection; the
native Lean/Lake import graph is authoritative for compilation order. Replace
the custom regex dependency resolver as an execution authority. A read-only
inventory may retain parsed import lines as navigation, but must not claim
complete closure on that basis. Implementation should obtain the module graph
through Lake/Lean's module/import facilities and reconcile it with actual build
jobs. Unsupported inventory extraction must fail the provenance phase.

Before any cache reuse, record a deterministic source snapshot containing:

- Repository commit plus reviewed target list, workflow, runner/audit generator,
  proof probe, lock/bootstrap/build helper hashes, root lakefile/manifest and
  lean-toolchain bytes. CI requires a clean reviewed source snapshot; a local
  dirty snapshot can produce diagnostics but is not commit-level acceptance.
- Each resolved package's name, source URL/type, manifest revision, actual Git
  commit/tree, configured source directory, package configuration and manifest
  hashes, and tracked content hashes. Exact package-root identity matters:
  `git -C dir rev-parse HEAD` must not fall back to the parent repository.
- Each module's canonical provider package and source path/hash, imported module
  identities, and transitive dependency fingerprint. Reject ambiguous module
  providers and unexpected search-path entries rather than choosing by accident.
- Actual Lean/Lake executable identities and version, OS/architecture, relevant
  compiler options, environment, and native-artifact dependencies. Record the
  root-resolved batteries/Cli pins, not merely Architect's historical requests.

Reject staged or unstaged tracked dependency changes, mismatched HEADs, missing
sources, untracked/ignored Lean or native source that can shadow a tracked module,
and unapproved symlink/provider escapes. Generated files within authorized
build directories are allowed, but are artifacts rather than source evidence.
Do not reject every `.lake` write or make dependency directories read-only.

Snapshot all tracked build-relevant package content conservatively; record the
resolved module closure separately. This avoids treating a bare package commit
as proof of the working-tree bytes actually used.

## Cache provenance and final stability

Prefer Lake's native dependency tracking with a new reviewed-lane cache schema.
Do not reuse the old custom copied-closure cache as native evidence. The current
fingerprint covers repo source, root toolchain string, Mathlib revision, and
repo dependency fingerprints; it omits Architect source and tool compatibility.
Its artifact hashes establish consistency with metadata, not trustworthy origin.

Cache keys must bind the complete source/dependency snapshot, compiler identity,
options/platform, audit-generator version, and schema. Restore only caches
produced by an allowed trusted run; fork/PR-produced cache entries are not
authoritative for protected-branch acceptance. Validate artifact file hashes,
relative-path containment, symlink policy, and required Lean artifact companions.
A matching hash in attacker-controlled metadata is not an authenticity proof.
Treat source/manifest mismatch as failure, and artifact corruption as a cache
miss requiring a clean rebuild. Never silently reuse a dirty provider's outputs.

Use fresh output directories per run. Recheck root inputs and every resolved
dependency's bytes, Git identity, dirty state and source-provider map after the
final audit/probe, including cache-hit runs. Rescan the source inventory so new
or removed files are detected. Any change invalidates acceptance and prevents
cache publication. Publish the final report atomically only after this check;
failed or interrupted runs keep diagnostic evidence with a non-success status.
No global cache deletion, dependency checkout/reset, or silent source repair.

## Audit completion contract

Keep the existing foundational axiom allowlist: propext, Classical.choice,
Quot.sound. Keep unsafe/partial rejection for selected owner declarations.
Continue enumerating actual environment declarations by their owner module,
including private/generated declarations and instances; no theorem-name regex
substitute. Audit each target's completion explicitly: the current single
global `count > 0` does not prove that all 65 targets contributed declarations.
Require a per-target count or an explicitly reviewed zero-declaration exception;
none is implied for these new nine owners. Audit both cache-hit and fresh-build
paths and retain the existing proof probe.

Architect supplies metaprogramming/attribute infrastructure. Do not apply a
blanket ban on unsafe implementation code to every dependency. Instead record
its exact source/build provenance, enforce the selected-owner audit, and reject
non-allowlisted axioms reachable from those declarations. This does not prove
the dependency metaprogram itself correct. Preserve warning logs and report
their exact scope; do not relabel successful compilation as warning-free.

## Test contracts for the implementation phase (not run)

| Case | Required result |
|---|---|
| Target-list preservation | Original 56 remain in order; all nine additions remain; 65 unique targets; no silent skip. |
| Native provider resolution | Triality retains `import Architect` and blueprint attributes; provider is the root manifest's LeanArchitect package. |
| Clean-pin compatibility | Fresh 54d3… source, root 4.34.1 and root batteries/Cli compile Architect without any local patch or Architect cache. Failure blocks the full lane with diagnostics. |
| Dirty dependency | Reproduce the observed Command.lean edit at unchanged HEAD; reject before compile/cache reuse. Existing oleans cannot override the rejection. |
| Wrong package identity | Wrong commit, parent-repo Git fallback, missing checkout, or unexpected provider fails preflight. |
| Package/toolchain mismatch | Root executable mismatch fails; dependency's historical 4.28 declaration is recorded; no implicit toolchain switch or manifest rewrite. |
| Closure completeness | Indirect Architect/Batteries imports, multi-import syntax and supported public imports are resolved natively; cycles/unknown providers fail. |
| Path packages | Atlas/GIFT missing, untracked, dirty or mismatched cases fail according to provenance rules; tracked InfoGeometryCore remains supported. |
| Cache invalidation | Change dependency source, package pin, tool identity, options, manifest, audit generator or target selection; old cache cannot establish acceptance. |
| Cache trust | Untrusted origin, forged metadata, path traversal, symlink escape, hash mismatch or missing companion artifact cannot produce a passing cached build. |
| Final stability | Change owner, dependency, manifest, probe, target JSON, or add a shadow source during execution; final report fails and no accepted cache is published. |
| Per-target audit | Omit one target's declaration coverage while other counts remain positive; fail. Reject sorryAx/custom axioms and selected-owner unsafe/partial declarations. |
| Lock and interruption | Busy lane runs no compiler; children remain guarded; interrupt cannot leave a passing stale report or release an active child's guard. |
| Preservation | Before/after hashes show no root pin, dependency source, proof import, attribute, gitlink, or submodule metadata modification. |
| Full acceptance | Native 65-target build, combined per-target audit, unchanged proof probe, clean provenance and stable final snapshot all pass in one reported run. Component success alone is not full CI success. |

Pure fixture tests may exercise metadata, inventory and cache rejection without
Lean. Clean-pin compatibility and full acceptance are real sequential compiler
tests requiring the shared lane and independent QA. No result is supplied here.
