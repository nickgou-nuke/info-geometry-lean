# Information Carnot validation record

Task date: 2026-11-18, Europe/Sofia.

## Acceptance state

Status: **draft; native compilation and all-declaration axiom acceptance
pending**. The initial diagnostic pass failed and its reviewed repairs are
included. The next local check is queued behind another task's genuinely held
canonical build lock. A dedicated GitHub runner provides an independent
exact-PR-head acceptance route. This checkpoint does not equate mathematical
review or static source scans with kernel acceptance.

Repository: `nickgou-nuke/info-geometry-lean`.
Branch: `codex/information-carnot-20261118`.
Base: `08c34e03f610b452e03422037949196dc7d92d6d`.
Lean: `leanprover/lean4:v4.34.1`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The development checkout has its own real Git directory and read-only object
alternates to an existing checkout. It is not a linked Git worktree. Native
verification uses a clean, separately initialized Mathlib at the tracked pin.
No Lake root or dependency directory was symlinked, no pinned dependency or
maintained gate was changed, and no cache directory was cleaned or removed.

## Provenance and owner review

The initiating message is preserved in
`docs/intake/information-carnot-20261118/prompt.txt`, including the GitHub app
mention and one terminal newline:

- UTF-8 bytes: **897**.
- SHA-256: `d72f9de47e64ded655359bd4b17ed3c21d8c35a033b0150da3a66315deee3a7c`.
- The adjacent manifest records its source, date, encoding and base revision.

The theorem contract records the carrier, conventions, construction, reused
owners, actual assumptions, and smallest missing implications. Repository
search covered the related names, declaration bodies, imports and consumers.
The navigation preflight had no installed declaration-DAG index; fresh graph
coverage is not claimed.

Independent non-authoring reviews covered the real CFC Gibbs construction,
ordered Duhamel trace derivative, actual affine isotherms and their interval
integrals, reciprocal scale segments, full matrix radial positivity/purity,
real conjugation and internal commutants, Gram dissipation and analytic return
obstruction, the exact logarithmic radial-to-Gibbs chart, and the legacy
zero-scale inconsistency. The integrating parent
reviewed the candidates and their exact diffs. Native API source inspection
informed repairs but is distinguished from compilation.

The existing `Physics.MatrixTraceBimodulePairingNative` is changed only at its
imports. Its declarations and proofs are byte-identical below the imports.
Four precise native imports replace the umbrella Mathlib and unused
FiniteSpinAlgebra imports. All eight inspected pre-existing non-aggregate
direct consumers explicitly import FiniteSpinAlgebra themselves. This bounded
consumer review is not a whole-repository native certificate.

## Diagnostic and repair record

The first four-target native pass completed with failures and no axiom audit.
Its exact source snapshot, report, logs, environment and compiled dependency
artifacts were preserved before incremental reuse.

- Gibbs needed the native rational normed-algebra instance derived from its
  existing real normed algebra, an explicit strict-positive/positive-definite
  equivalence, and an explicitly typed trace-product derivative.
- Radial normalization needed an explicitly qualified scalar inverse law;
  unused simplifier arguments were removed.
- The Gram proof needed the native real inner-product symmetry in the required
  orientation and explicit inclusion of its proof-only section hypotheses.
- Carnot was blocked by the Gibbs failure in that initial run.
- Source review found the same rational-algebra instance dependency in the
  real unitary exponential-naturality theorem.

The staged gate initially did not recognize the existential noncommuting
witness in its `¬ Commute` form. The actual matrix witness was restated as
`∃ K R : Matrix (Fin 2) (Fin 2) ℝ, K*R ≠ R*K ∧ ...`, retaining the skew
generator, positive trace-one state and orthogonality. This is the same
mathematical proposition in the gate's supported native syntax. No checker or
theorem hypothesis was weakened.

## Native verification method

The maintained `tools/quality/check_clifford_dirac.py` accepts explicit owner
targets, snapshots their entire repository import closure, verifies the exact
Mathlib/toolchain pins and clean dependency source, and compiles under the
canonical shared build lock. Exactly one local compiler owner was used.
Waiting for another task's lock did not trigger a competing compiler, cache
mutation or process termination.

Incremental reuse is limited by that checker's source/dependency fingerprints,
Lean version, successful prior exit status and generated-artifact hashes. All
changed sources and dependents are recompiled; the declaration audit remains
enabled. The audit enumerates every declaration owned by a selected target,
including private and generated constants. Its allowed foundational axiom
union is a subset of `propext`, `Classical.choice` and `Quot.sound`.

The focused workflow additionally asserts zero compiler warnings in every
selected target. Warnings in unchanged dependencies are reported separately.
Its exact-PR-head source fetch avoids traversing unrelated external submodules;
the tracked dependency pins still control native verification.

## Source gates

For every changed Lean owner, the maintained strict placeholder scan is run:

```bash
python3 tools/quality/placeholder_audit.py --root <owner-path> --strict
```

The maintained semantic gate is run on the same selected owners:

```bash
python3 tools/quality/semantic_vacuity_gate.py <owner-paths> --fail-on error
```

These source scans are heuristic checks. Their supporting-API notices are
reviewed independently of compiler warnings and native axiom results. The
tracked staged proof gate is installed through `core.hooksPath=.githooks` and
is required on the actual commit; its installation alone is not evidence that
the commit passed it.

The final static pass on the eight selected owners exited successfully:
strict placeholder scans had zero hard findings; the semantic error gate had
zero errors and 16 reviewed supporting-API notices. YAML parsing, syntax
parsing of the workflow's shell and four embedded Python blocks, intake byte
count/checksum verification, and staged whitespace checks passed. These static
checks launch no compiler, Lake process or test suite.

## Acceptance boundaries

The acceptance scope is the selected owners, their exact repository source
closure and the combined native declaration audit. It is not an exhaustive
repository build or a successful root pre-push gate. Earlier root jobs on the
same base encountered unrelated external-submodule and case-collision issues;
those are outside this source change.

The contract separately records physical and analytic boundaries: a radial
purity law is not a general entropy monotonicity theorem; an orbit is not
automatically an entire entropy level set; a prescribed solution theorem is
not ODE existence or convergence; the equilibrium cycle does not construct
reservoir dynamics or finite-time power; and no Gromov--Witten, spacetime,
Goldstone, NESS or causal-wave identification follows without its own map and
compatibility proof.

## Initial publication source snapshot

The resolver identifies **44 repository source modules** and **54 native import roots**
for the eight selected targets (seven new owners and the import-refined trace
action owner). No whole-Mathlib umbrella import remains in this closure.
The strict scan reports 17 reviewed soft notices, separate from compiler warnings.

| Selected owner | Source SHA-256 |
| --- | --- |
| `Thermo.RealMatrixGibbs` | `e0be58ee31a0a48b4b5ef1a55d04d3bbf117d20af4a1c38c03f6bbfbfbc07b5a` |
| `Thermo.RealMatrixCarnot` | `145bcd398a261442af4147b31537989d32585e8cacfe82e479fe78d5a6d2c8d6` |
| `Thermo.RealDensityRadialFlow` | `ec98849aa978ad38b46caa7268482146a07df3064cf94510dacacda6ff7b7a77` |
| `Thermo.RealMatrixGibbsOrbit` | `fdddf796e31db0ec7d8525c3817d3752e724811677ce8b325157953cd3d5948d` |
| `Thermo.RealMatrixGibbsRadialChart` | `a4d704c06e74762288cfcdf70970f69cc64df41f3c0a2f3e5c012c38c98dde03` |
| `Thermo.GramMetriplecticNoReturn` | `9b99e33ccf14bc9c0dbb14e09e84ba831a6a7cbc10766871843eae3366aba08f` |
| `Canonical.WeylEntropyScaleObstruction` | `d33caf42e6a16c4d2afa308b62a6f877ff70a884358c5faee9a52fb6d4435eb7` |
| `Physics.MatrixTraceBimodulePairingNative` | `d0a401304bb5e89b6879e2f36cbad78a01a66b09f444ab307f961c351d064d6c` |

The focused native command is:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root ../mathlib --output ../information-carnot-report \
  --target InfoGeometry.Thermo.RealMatrixGibbs \
  --target InfoGeometry.Thermo.RealMatrixCarnot \
  --target InfoGeometry.Thermo.RealDensityRadialFlow \
  --target InfoGeometry.Thermo.RealMatrixGibbsOrbit \
  --target InfoGeometry.Thermo.RealMatrixGibbsRadialChart \
  --target InfoGeometry.Thermo.GramMetriplecticNoReturn \
  --target InfoGeometry.Canonical.WeylEntropyScaleObstruction \
  --target InfoGeometry.Physics.MatrixTraceBimodulePairingNative
```

The workflow is `.github/workflows/information-carnot.yml`. It uploads the
report, compiler logs, generated audit source, semantic report and evidence
hashes. A successful report plus zero warnings in all eight targets is
required for focused native acceptance. Source publication or a queued job
does not establish that result.

## Native diagnostic repair checkpoint: 2026-11-18

The first focused CI run `44272862706`, job `134693554733`, checked exact
source `c123b055fb974dc9825e3b312be6864ae913667c` and tree
`64a0886b9fcf965bb211e5137efa46ffc5cbeeb2`.
It processed all 44 repository modules: 40 compiled, Gibbs alone failed, and
Carnot/orbit/radial-chart were blocked by that dependency. The radial-flow,
Gram no-return, Weyl obstruction and import-refined trace-action targets each
compiled with zero warnings. The failed run did not execute a successful
axiom audit.

Artifact `14414202924` was downloaded and independently checked: ZIP SHA-256
`7dba8751321d8f76a9940d2fed79d2ceefe4f0311c129d948363b716f2dac41b`.
All 46 evidence-manifest hashes and all 44 source hashes matched the exact
snapshot. The subsequently completed local seven-target pass independently
reproduced the same two Gibbs diagnostics; its complete evidence was preserved
before another incremental attempt.

The source repair is deliberately narrow:

- `Function.comp_def` and `Pi.mul_apply` expose the same function composition
  and ordered matrix product in the entropy trace derivative, allowing the
  existing trace evaluation lemma to apply.
- The `omit` scope precedes its theorem doc comment, fixing the parser error
  without changing which assumptions are omitted.
- The identical composition/product normalization is applied to Carnot's
  matrix first-law derivative, which uses the same native composition shape.

No theorem statement, mathematical assumption, matrix product order, instance,
dependency pin or gate is changed. Independent source/API review passed. Strict
and semantic scans of the two changed owners passed with zero errors, the
staged proof gate passed, and the installed commit hook remains required.

The changed source hashes are:

| Owner | Repair SHA-256 |
| --- | --- |
| `Thermo.RealMatrixGibbs` | `e8d322157c18dad41e8343dcbbb3d99c28ccbd49a9bdce29bb06240748c92b43` |
| `Thermo.RealMatrixCarnot` | `7cdb063ec4289db5887f78398379fa094ad07eac91a2f54782db6c7ae46bb813` |

The remaining six selected source hashes are unchanged from the initial
publication table. The full eight-target incremental local check and the
exact-head CI workflow are the native acceptance routes. Both retain the
complete declaration audit and selected-target zero-warning requirements.
