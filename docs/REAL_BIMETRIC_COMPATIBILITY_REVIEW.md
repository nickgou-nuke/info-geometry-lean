# Real bimetric compatibility: source and verification record

## Source identity and scope

The [theorem contract](REAL_BIMETRIC_COMPATIBILITY_CONTRACT.md) records the
intake hash, actual native carriers, operator conventions, corrected
implications, and excluded claims. The source starts at upstream `main`
`08c34e03f610b452e03422037949196dc7d92d6d`. No earlier draft PR is an import
dependency. The unchanged environment is Lean `leanprover/lean4:v4.34.1` and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

| Owner under `lean/InfoGeometry/` | Source inventory | SHA256 at independent source review |
|---|---:|---|
| `Geometry/SymplecticMetricCompatibility.lean` | 12 theorems, no definitions | `f5d5c05645889ed2e814c786da628ba940fde729df81c44b67d995d4024aaf90` |
| `Geometry/ObliqueSymplecticInvolution.lean` | 33 theorems, 5 definitions | `54789375d49e3f0781ed71f8395d4dd8964d8d3a4e9fc53590ff6cfa1c54c02c` |
| `Clifford/PhaseSpaceSymplecticMetricCompatibility.lean` | 8 theorems, no definitions | `105c8c5d062a7f24c114236f54bc4a30a18a76fa3d2c44578d378d71d4349546` |

These are lexical source counts, not the native audit's count of all owned
declarations. All three owners are imported by `InfoGeometry.All`.

## Independent mathematical review

Generation, mathematical/source review, and acceptance QA are separate roles.
The independent reviewer inspected every candidate statement and proof,
matched the native APIs against the pinned Mathlib source, and checked the
actual existing phase-space definitions. All three exact hashes received
source fidelity PASS. No required mathematical or hypothesis correction was
found. The review receipt has SHA256
`542791502c32aded02c370263816b50c808125aa735e7e4736375da34d9b1b37`.

The source review specifically checked:

- The isometry/anticommutation equivalence uses only right separation,
  involutivity, and reversal of the original form.
- The comparison map is `-(K*I)` before anticommutation; no exchange of
  noncommutative factors is implicit.
- Both contradiction theorems retain `Nontrivial E`.
- The counterexample has the correct complex sign, actual positive metric,
  genuine native eigenspace spans, equal one-dimensional finranks, isotropy,
  and both failed operator relations.
- The phase-space consumer uses `-phase G`, retains projectivity for its
  imported nondegeneracy theorem, and does not infer positivity from a merely
  symmetric duality equivalence.

This is a mathematical and source/API result. It does not establish Lean
elaboration, compiler warning counts, or declaration axiom dependencies.

## Initial commit-gate rejection and proof repair

The actual first installed pre-commit hook exited 1 on eight OpenGauss T16
findings. Its source-level operator classification did not recognize several
intermediate scalar readbacks. No commit or native check resulted from that
attempt. The failed receipt is retained.

The repaired source uses direct negation, alternation, order and additive
cancellation proofs for the flagged steps. The concrete owner additionally
proves the full matrix pullback `K_aᵀ * Ω * K_a = -Ω` entrywise and transports
it through native `Matrix.toBilin'_comp`. All prior theorem types are
unchanged; this adds one substantive matrix theorem. The consolidated source
review covers the repaired hashes above. The installed gate and its policies
remain unchanged. The actual installed pre-commit retry passed at source
checkpoint `8c6224c4fb1d920b0500eea02df8a3540aceeff6`.

## Owner search and dependency closure

The independent bounded survey inspected 47 related owner/consumer files.
All matched the stated main revision. Closest owners included the existing
Kähler triple, para eigenspace/dimension results, flat split-quaternion
family, doubled chiral/Krein constructions, native Clifford/matrix
equivalence, and the actual neutral phase-space and generalized-metric
constructions. Existing inverse-form uniqueness and finite-dimensional
representation APIs were inspected directly in Mathlib.

The new owners' exact source closure contains 20 repository modules and 36
Mathlib import roots. The maintained lexical traversal and an independent
comment-aware traversal agree. All native import roots exist in the pinned
Mathlib checkout, and all 17 reused repository modules match the base bytes.
This is source-import evidence, separate from a compiled dependency result.

## Verification status at the initial source checkpoint

As of 2026-11-17, all three candidates have independent source review PASS.
The local shared build lock is occupied by an earlier validation lane. This
change does not cancel that lane, remove its lock, modify the pins, or replace
the maintained build helpers.

The following results remain pending at this documentation checkpoint:

1. The independent static gate sequence on the final frozen snapshot.
2. Native elaboration of the selected owners and their source closure.
3. Zero compiler warnings for each selected owner and the complete native
   owned-declaration axiom audit.
4. The actual push/root integration gate, including `InfoGeometry.All`.

The PR body and attached run artifacts record subsequent outcomes with their
exact revisions and commands. A draft publication, a source review, and a
static gate exit code do not constitute a successful native or root build.

## Focused native workflow

`.github/workflows/real-bimetric-compatibility.yml` invokes the unchanged
`tools/quality/check_clifford_dirac.py` with these exact targets:

```text
InfoGeometry.Geometry.SymplecticMetricCompatibility
InfoGeometry.Geometry.ObliqueSymplecticInvolution
InfoGeometry.Clifford.PhaseSpaceSymplecticMetricCompatibility
```

The workflow checks the exact PR source head and unchanged toolchain/Mathlib
pins, hydrates only the observed native import roots under the maintained
shared lock, and compiles fresh repository artifacts. It uses no
`--incremental` and no `--skip-audit`. It explicitly rejects any compiler
warning in a selected owner, since the helper's historical automatic warning
filter alone does not cover these namespaces.

The native audit must inspect every declaration owned by the selected
modules and permit only `propext`, `Classical.choice`, and `Quot.sound`.
Compilation of imported source modules and axiom auditing of selected owned
declarations are distinct coverage statements.

The workflow triggers on the full repository source closure, integration
imports, verification helpers, pins, and its documentation/configuration.
It may restore pinned dependency artifacts; it does not restore repository
proof artifacts. Cache writes are restricted to manual dispatch under the
repository's trusted-event policy.

Source provenance records the checked source revision separately from the
executing workflow revision. The live outer driver log is stored below
`driver/`, outside the maintained checker's top-level evidence-hash glob.
Independent native acceptance must reconcile the run, complete source/helper
hashes, pins, warning counts, fresh compilation records, all axiom records,
and the downloaded artifact bytes. An incomplete or queued run is pending,
not accepted.

This focused workflow does not certify the root Lake package or
`InfoGeometry.All`. Those gates remain required separately.

## Native elaboration repair, 2026-11-17

The reattached `Pasted text(20261117-125255).txt` has the same 33,409-byte
content and SHA256 as the original intake recorded in the contract. The
continuation therefore repairs this existing PR rather than creating another
owner for the same statements.

The [first focused native run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44065838743)
checked source `bf4d94533f76834e325b5c36725fb76f00481260`. Its downloaded
evidence ZIP was verified against SHA256
`70d9a2c89ebbf78fe4333d3b6a593a2d9946ecf12375b6cbb82c0d7afda83bae`.
The general owner compiled with a deprecated-import warning; the oblique
owner failed to match a transported `Matrix.toLin'` equality to its bundled
endomorphism target; the phase-space consumer had an additive rearrangement
goal and rewrites resolving to specialized imported negation lemmas.
The native axiom audit was not reached in that run.

The repair preserves every one of the 53 theorem statements and all five
definitions:

- Replace the deprecated real-number forwarding import with its native
  `Mathlib.Basic.Real.Basic` owner at the unchanged Mathlib pin.
- Expose the actual `Matrix.toLin'` compositions and identity in the
  anticommutator transport, retaining both ordered products.
- Qualify the intended root ring identities in the phase-space consumer.
- Expand the two form-evaluation readbacks through their native owner
  lemmas before simplifying their scalar expressions.
- Remove only the tactic sequencing and unused simplifier arguments
  identified by the failed native run.

The explicit form readbacks also resolve the earlier skeletal/trivial-surface
heuristic findings without changing the scanner or any theorem contract.
The renewed semantic audit with `--fail-on warning` reports zero findings.
Independent source review, the installed commit hook, the focused compiler
and complete axiom audit, and the root integration gate remain separate
checks. The PR records their latest outcomes and exact checked revisions;
this repair history does not itself assert a native or whole-package pass.
