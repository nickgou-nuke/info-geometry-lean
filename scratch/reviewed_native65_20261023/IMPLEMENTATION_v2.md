# Native reviewed65 v2 — response to A-A, not CI acceptance

New candidate `native_reviewed_v2.py`; original candidate and contract untouched.
No tests/builds run, no live files/dependencies/pins changed. Parent must review
and promote; this does not bypass Atlas/GIFT or dirty Architect blockers.

## Exact selection and integration order

Read current native JSON: **56**, not 65. Read upstream
`81867ee217620005c5c18c4cb78b15f8d24f68db:tools/quality/reviewed_prs_20260921.json`:
the same ordered 56 plus these ordered nine:

1. InfoGeometry.Canonical.DrazinShellCascade
2. InfoGeometry.Canonical.DrazinInterShellHodge
3. InfoGeometry.Core.DiracPeirceSuperalgebra
4. InfoGeometry.Core.SupercolorMultiplication
5. InfoGeometry.Routing.AttentionReadoutCompression
6. InfoGeometry.MassSpectrometry.MolecularIdentifiabilityBridge
7. InfoGeometry.Algebra.CuntzTensorQuotientPositivityObstruction
8. InfoGeometry.Canonical.MajoranaCoefficientAction
9. InfoGeometry.Canonical.MajoranaPfaffian4

V2 contains the literal ordered 65 tuple and compares tuple equality, not length
or a set. A replaced/reordered 65 or the present 56 fails before output creation.
It neither appends targets silently nor accepts an alternate selection argument.
Parent should first review/promote the nine additions to the native selection,
then the optional native mode. Do not enable a supposedly reviewed65 job against
56. The existing copied mode can remain the default and keep its old argument
contract. Native mode branches before Mathlib path resolution/copied closure.
No fallback on failure. No exclusion of the Architect-importing owner.

Suggested promotion: helper becomes `tools/quality/reviewed_native.py`; optional
`--mode native` calls `run_native` from root, with `wait`, optional approved
cache receipt and externally trusted digest. Keep `--mode copied` default;
`--mathlib-root` required only there. Reject copied-mode cache/mathlib overrides
in native mode. All helper public axiom/role/count/probe reuse from v1 remains.

## Actual pinned Lake layout and Paperproof

Read installed 4.34.1 `Lake/Load/Config.lean` `LoadConfig.configDir`:
`cfg.wsDir / defaultLakeDir / "config" / toString cfg.pkgIdx`.
`Lake/Load/Lean/Elab.lean` writes configuration olean, trace and lock there.
V2 inventories/rejects preexisting **workspace `.lake/config`**, across all
package indices. The old `.lake/lakefile.olean` assumption is removed.
No cache deletion is offered. Use a fresh workspace configuration area.

Manifest Paperproof has `subDir: "lean"`; checked source
`.lake/packages/Paperproof/lean/lakefile.lean` defines the native package.
V2 distinguishes checkout root (`.lake/packages/Paperproof`) for Git HEAD,
cleanliness, gitlinks and complete source inventory from package root
(`.../Paperproof/lean`) for config and `.lake/build` artifacts. `subDir` is
containment-checked; symlink path components are rejected. Other contained
subDir packages use the same native handling. No alternate lakefile.

## Cache trust split — usable warm dependencies, strict root/Architect

Root `.lake/build`, Architect package `.lake/build`, and workspace `.lake/config`
must initially contain no files. They are produced by this native run. No dirty
Architect-era olean is trusted even when HEAD equals 54d3... . Clean pinned
Architect source must compile under root 4.34.1; failure stays failure.

Other packages, including Mathlib, may carry warm build artifacts only with an
**externally trusted cache receipt**. Existing `pantograph_environment` records
context but is not an authenticated build receipt; bootstrap is path preflight,
not artifact authentication. V2 adds only missing cache acceptance comparison.
It does not invent a cache producer or claim that locally hashing old oleans
establishes provenance.

Receipt schema:

```text
schema: reviewed-native-dependency-cache-v1
configs: exact root lakefile/manifest/toolchain/.gitmodules SHA256 map
packages:
  <each warm package name>:
    source:
      entry: exact root manifest package entry
      provenance: exact checkout HEAD and recursive gitlink identities
                  (or root commit for tracked in-tree path package)
      sources: relative-path -> SHA256 of actual source inventory,
               including ignored files, excluding enumerated generated locations
    artifacts: package-relative .lake/build path -> SHA256, ALL regular files
```

Pass receipt path and its approved SHA256 separately. Digest must come from a
protected CI policy/artifact channel established by parent review, not from the
same untrusted checkout/cache bundle, user-discovered local hash, or PR-controlled
workflow input. A matching digest authenticates only as strongly as that trusted
channel. Producer must attest a successful clean exact-pin build with the same
pinned toolchain image/config/source identities; no dirty dependency admission.
V2 verifies exact content equality, rejecting unknown/extra/missing entries.
No root/Architect/config-cache receipt exception. Without a trusted producer or
approved receipt, warm caches fail closed; cold dependencies can still build.
Establishing that producer/channel is an integration prerequisite, not completed
by this sandbox. Large dependency inventories are deliberate and may cost I/O.

## Network and filesystem boundaries — corrected scope

`--offline` controls Lake dependency resolution. `--no-cache` and `--rehash`
control Lake cache/hash behavior. **None isolate network access or authenticate
arbitrary artifacts.** Committed Lake configuration and build commands can spawn
ordinary programs, including network clients. V2 makes no network-isolation claim.

The required CI launcher must enforce OS/container network egress denial for the
whole job and child process tree, after provisioning approved source/cache inputs.
Use a pinned toolchain image and an externally enforced sandbox/network policy
(e.g. a container launched with network disabled by trusted CI configuration),
without host credentials, socket mounts, or host package/build mounts. Keep source
checkout and approved cache inputs under exclusive job ownership; permit only
needed native generated output writes. A CLI boolean/environment variable is not
proof that this policy exists. Python cannot verify host firewall policy reliably,
so no pretend check is included. Policy enforcement evidence belongs to CI launch
provenance. Do not promote this to an isolated-CI claim without that launcher.

## Source and path scope

- Uses existing bootstrap path preflight first: Atlas untracked/GIFT dirty fail.
  Every installed manifest git entry is then checked at exact HEAD and clean
  Git status; dirty Architect fails independently once earlier blockers are fixed.
- Actual filesystem inventory, not only git ls-files: dependency checkout trees
  and root `lean`, `tools`, `proofs` include ignored files. Root metadata is hashed.
  Source/artifact symlinks and symlink ancestors are rejected, not followed into
  unbound targets; unreadable/special inventory files fail.
- Git package and gitlink path-package nested gitlinks recursively require each
  recorded commit, initialized checkout, clean status and contained path. Their
  files enter the parent inventory. In-tree tracked path packages containing
  nested gitlinks fail explicitly pending a provider mapping; no silent omission.
- Excluded generated locations are the package-root `.lake/build` and workspace
  `.lake/config`; their initial artifact policy is checked separately. Other
  generated files written into inventoried sources cause final drift failure.
  This may need targeted parent review for genuine native generators; do not
  blanket-ignore ignored source directories to suppress failures.
- These inventories do not prove every arbitrary file a custom build script
  could read is bound. Unrelated scratch/scripts/external host inputs are not
  silently declared part of the audited source closure. The trusted config and
  restricted CI filesystem policy are essential; adding a new source provider
  requires inventory expansion before claiming coverage.

Output is restricted to fresh `scratch/native_reviewed_runs/<single-run-name>`.
Before mkdir it rejects traversal, symlink ancestors, existing directory, lack
of Git ignore rule, and overlap with configured path/package providers. It
cannot point at dependency/build/source trees. Invalid intake emits CLI failure;
no old report is reused. No filesystem race resistance against hostile concurrent
writers is claimed: exclusive CI job ownership is required in addition to lock.

## Runner and preserved audit semantics

Shared BuildLock and inherited fd remain. Every compiler is synchronous; Ctrl-C
waits without killing the child. Runner explicitly permits only `input`, `check`,
`capture_output`, `text`: requires captured text; supports string/None stdin;
rejects unsupported kwargs. `check=False` returns the actual nonzero result to
the existing context helper, which rejects it. Default calls require zero exit.
Launch failure creates a command row with `exit_code: null`, status
`launch_failed`, empty stdout log and traceback stderr log. Terminal failures
retain separate logs and actual return code. Final report remains failed.

Full65 native build, fresh source execution of both command-only targets, public
axiom helper/count parser, original probe, source stability and existing context
fingerprint reuse remain. Context hashes cover the actual dependency query's
reported inputs, not a falsely claimed recursive artifact attestation. Native
closure comes from root Lake; there is no copied-Mathlib resolver or new theorem.

## Deferred A-A/QA contracts — no execution claimed

Review source then test serially under the shared lock: actual .lake/config index
cache rejection; warm correctly attested Mathlib acceptance and dirty/mismatched/
extra/missing cache rejection; cold Architect requirement; Paperproof checkout vs
package root; wrong/dirty/uninitialized nested gitlinks and tracked-path nested
rejection; ignored source drift, symlink and unreadable file rejection; exact65
order/substitution/56 rejection; safe output checks before any mkdir; runner
stdin delivery, kwargs rejection, launch failure receipt, nonzero/context-helper
propagation, interrupt lock retention. Confirm source/artifact inventory behavior
against the pinned native packages before live promotion.

Integration prerequisites still open: parent promotion of exact nine targets,
approved dependency-cache producer/receipt channel, trusted network-isolated CI
launcher, clean recorded Atlas/GIFT/Architect sources and native prerequisite
availability. None authorize pin/source updates or dropping owners. Parent A-A/QA
then locked execution decides acceptance; this version has no test/build PASS.
