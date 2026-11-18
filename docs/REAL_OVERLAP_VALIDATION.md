# Real overlap validation record

## Source checkpoint: 2026-11-17

Status: **draft; native compilation and declaration axiom acceptance pending**.
No source review or heuristic gate is presented as kernel acceptance.

Repository: `nickgou-nuke/info-geometry-lean`.
Branch: `codex/real-overlap-geometry-20261117`.
Base: `08c34e03f610b452e03422037949196dc7d92d6d`.
Lean: `leanprover/lean4:v4.34.1`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The independent sparse checkout has its own Git directory and read-only object
alternates to an existing checkout. It is not a linked Git worktree. No Lake
root or package directory was symlinked, no dependency pins or maintained gates
were changed, and no cache directory was cleaned or removed.

## Provenance

The input `Pasted text(20261117-140557).txt` is preserved byte for byte as
`docs/intake/real-overlap-20261117/overlap-vacua-raw.txt`:

- Bytes: **41,814**.
- SHA-256: `460d8aa3e1bf4c8c393c009a8677d60f31649fdc883e989094077c26f1ecf230`.
- Adjacent manifest records its original name and base revision.

The claim/reuse contract records which input claims have complete candidate
proofs, which require correction, and which remain outside these owners.
Primary publications were consulted as contextual evidence, not as a
substitute for native proof checking.

## Reviewed source

| Selected owner | Source SHA-256 |
|---|---|
| `Algebra.OverlapInvolutionPair` | `6baee4fad4f4a1ddbab63e5f71dc59aa8d412de5b74a08ed068b01197e9840ea` |
| `Canonical.RealDomainWallTransfer` | `ffe49c3c2c2e16c40a78585e41a68a2f0b8568335c0a40d789c93a688f2479aa` |
| `Canonical.RealPhaseRayProjector` | `3fc225d9c09ca54c40251ca93d6cee8f333eafbf2109e19a5bbe3a2639f4810f` |
| `Canonical.RealPhaseRayProjectorDoubled` | `bc2a16cc668bb4ad486971077ff08b2db89c0d10bffe4fabd7a28df6dde5abab` |

Each owner received review by a non-authoring agent and by the integrating
parent. Review checked the exact noncommutative residual, modified-chirality
sign, star-normality hypotheses, ordered transfer factorization, strict
positivity and actual inverse laws, Wilson Gram expansion, both phase rotation
signs, real trace normalization, the native doubled carrier, and the metric
boundary between observer and Krein forms. Native API signatures were inspected
at the pinned Mathlib revision. That inspection does not establish elaboration.

The native closure resolver finds **22 repository modules**, including four
targets, and **34 distinct native import roots**. Some unchanged dependencies
import the Mathlib umbrella; this task does not introduce a broad import into
its new owners or claim the roots are a count of all transitive Mathlib modules.

## Checks actually executed

For every selected owner:

```bash
python3 tools/quality/placeholder_audit.py --root <owner-path> --strict
```

All four runs exited 0, with **zero hard findings** and seven total soft
notices. Supporting evaluation identities and section assumptions were reviewed
at their types; no proof hole, authored axiom, or bypass was introduced.

The maintained semantic gate was run on the four exact source files:

```bash
python3 tools/quality/semantic_vacuity_gate.py <four-owner-paths> --fail-on error
```

It exited 0 with **zero errors** and six supporting-API notices. These are
heuristic notices, not compiler warnings or axiom results.

The tracked staged proof gate is installed through `core.hooksPath=.githooks`.
It passed on the actual staged source. Its first run identified four scalar
arithmetic steps inside phase-operator declarations and a matrix witness whose
conjunction ordering obscured carrier recognition. The proof repairs use native
scalar equalities, bilinear symmetry, and the existing trigonometric identity.
A reusable existential theorem now constructs the actual noncommuting
self-adjoint involutions before the stronger overlap witness consumes them.
No checker, pattern, tactic restriction, or theorem hypothesis was weakened.

Authored-file whitespace checks passed. The workflow YAML and its embedded
Python blocks parsed successfully. The intake byte count and hash match the
uploaded source. Generated compiler output is not committed as source.

## Native acceptance command

The maintained exact-source checker is used without changing its implementation:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root ../mathlib \
  --output ../real-overlap-report \
  --target InfoGeometry.Algebra.OverlapInvolutionPair \
  --target InfoGeometry.Canonical.RealDomainWallTransfer \
  --target InfoGeometry.Canonical.RealPhaseRayProjector \
  --target InfoGeometry.Canonical.RealPhaseRayProjectorDoubled
```

The focused workflow fetches the exact PR head without traversing unrelated
external submodules, reads the tracked toolchain and dependency revision,
fetches pinned native import caches under the canonical build lock, and
compiles the complete owned source closure. It then generates a native audit
for all declarations owned by the four targets, including private/generated
declarations. It requires both `report.status = passed` and zero compiler
warnings in every selected target. The allowed foundational axiom union is a
subset of `propext`, `Classical.choice`, and `Quot.sound`.

The workflow uploads the report, all compiler logs, generated audit source,
semantic report and evidence hashes. Its name is
`Real overlap geometry kernel check`; its file is
`.github/workflows/real-overlap-geometry.yml`.
Queueing or publishing this workflow is not native acceptance.

### Local runtime limitation

No new local compiler was launched for these owners. Earlier task checkers
lost execution-session visibility. Read-only diagnostics established genuine
contention on `/tmp/info-geometry-build.lock`, while each available command's
PID namespace was unable to enumerate the holder or possible old waiters.
An absent process in that view does not establish global absence. Earlier
source/output snapshots are preserved, the lock is unchanged, and no process
was killed. The focused remote job is the intended native acceptance route.

## Acceptance boundaries

Native acceptance must be reported at its exact source revision and actual
warning/axiom result. A successful focused check is not a whole-repository build
or a successful root pre-push gate. Earlier root jobs on this base encountered
unrelated submodule-resolution and case-collision failures; those files are
outside this change.

The new finite operator statements do not construct spectral sign calculus,
an infinite transfer limit, a Fock determinant, a determinant-line section,
Berry curvature, a local chiral gauge measure, anomaly cancellation, or a
classification of topological sectors. The source contract lists the missing
implications explicitly. The supplied-sign, positive-matrix, and real-phase
branches have no unproved connecting arrows hidden in structures or names.

## Native diagnostic repair checkpoint: 2026-11-18

The first focused run `44105266727`, job `134115770037`, completed with
native failures at source `3a89f43c1d3bb5a6e7ccc28aa5d3504345342be6`.
It did not reach a successful all-declaration axiom audit. This supersedes the
earlier queued checkpoint without erasing that historical source record.

The reviewed repair changes only proof/API details:

- After the native unitary cancellation, the two ordered adjoint-square
  proofs close their remaining additive identities with `abel`.
- The block quadratic form uses the actual finite sum over the sum index,
  including the native star/composition evaluation rules.
- The transfer owner imports the native real star-order instances explicitly.
- A redundant `rfl` after a closing rewrite is removed from idempotence.
- Three real doubled-space lemmas omit an unused completeness instance.

No mathematical conclusion is weakened. The proof/API delta received a
non-authoring source review and parent inspection; native revalidation is
pending. The same focused workflow checks the repaired exact PR head,
requiring all four selected targets to compile with zero warnings and every
owned declaration to have only the allowed foundational axioms.

Strict placeholder scans passed on all four repaired owners with zero hard
findings. The semantic error gate passed with zero errors and six reviewed
supporting-API notices. The actual repair commit uses the installed static
proof gate. No compiler, dependency pin, checker, or cache is changed by this
repair. The separate information-Carnot branch is not a dependency.

| Repaired owner | Source SHA-256 |
| --- | --- |
| `Algebra/OverlapInvolutionPair` | `bce130b96e206f79c8633e736974275b70f6157fcd9a3cde62c2d9a2dff53b45` |
| `Canonical/RealDomainWallTransfer` | `763898922652bb72488522a8696fbbab9ba6633879ba0525f7a41e3678689abc` |
| `Canonical/RealPhaseRayProjector` | `9501022ea4ca3b75ffb19c2602cb1ebed8aee66b1890419460cae046295d75e5` |
| `Canonical/RealPhaseRayProjectorDoubled` | `c13ad338e11758e9398c4d64ea6f26adb1043b5a43c9a362cdb2f3e9a045f8b1` |
