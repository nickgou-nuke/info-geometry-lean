# Replacement thermal relaxation: review and validation

Date: 2026-11-18. Scope: the three selected canonical owners and their repository
import closure. This record does not certify all historical files or a complete
thermodynamic engine.

## Owners and roles

| Owner | New construction or result |
| --- | --- |
| `Quantum/ReplacementRelaxation.lean` | Existing replacement projection; full matrix relaxation family; composition and centered action; fixed-target return obstruction; positivity at every finite amplification; exponential time path and actual derivative. |
| `Quantum/ReplacementHamiltonian.lean` | Exact ordered derivation defects; stationary-target covariance; radial/star-trace orthogonality; combined linear generator; trace-energy readouts and finite control bookkeeping. |
| `Quantum/ReplacementGibbs.lean` | Actual CFC Gibbs target; skew generator `(-Complex.I) • H`; stationarity, covariance, radial pairing, and energy readouts. |

Generation and independent review used separate agents. The parent integrated
the candidates and runs decisive compiler/audit checks. Review read the actual
replacement, ancillary amplification, inner-derivation, cyclic trace,
functional-calculus Gibbs, normalized-density, and matrix-entropy owners.
The derivative API and its scalar conventions were also checked directly in
the pinned Mathlib source.

The coefficient carrier is complex matrices because the existing positive
channel and CFC Gibbs constructions use it. Rate, time, and physical convex
parameters are real. No associative binary representation of octonions,
Krein-to-positive identification, or real/internal-complex equivalence is
asserted by these files.

## Exact receipt source identity

The observed PR #406 compiler and axiom-audit receipt covers source head
`9d03ea978991bb77cd815382bc851eaac28c5d9d`. Its three Lean owners have the
following SHA-256 hashes. These identify the receipt's source bytes. The
subsequent warning cleanup requires a fresh exact-source receipt; no later
head is certified by this historical receipt.

The subsequent cleanup removes exactly two unused `Matrix.mul_smul` arguments
from `simp` lists. Its Hamiltonian owner has SHA-256
`e2f1c876f568c5b7fa79181a02d36a3dc25496d94e558bd2f441e4496be186fc`;
the other two owner hashes are unchanged. Exact-head acceptance of this
cleanup is reported in the
[PR #406 checks](https://github.com/nickgou-nuke/info-geometry-lean/pull/406/checks).
The historical source table below remains tied to `9d03ea978991bb77cd815382bc851eaac28c5d9d`.

| Source under `lean/InfoGeometry/Quantum/` | SHA-256 |
| --- | --- |
| `ReplacementRelaxation.lean` | `e1bb590c1a5f61d6fd6c11cf18d2841748314563cb2f8e14aa4032456cd327bc` |
| `ReplacementHamiltonian.lean` | `8e21ac22b7db918208c75b4dd3140e1f72ecb5fa898dc3f7b4f5ca2a8e6cc5c3` |
| `ReplacementGibbs.lean` | `bebe57a34786fa4b1abfa3c43c7532cef4738602f522c1d70cbc9a2332aca6a1` |

## Matrix norm and scalar conventions

`ReplacementRelaxation.lean` imports
`Mathlib.Analysis.CStarAlgebra.Matrix` and opens
`Matrix.Norms.L2Operator`. Mathlib transports the continuous-linear-operator
norm on finite-dimensional Euclidean spaces to the existing matrix carrier.
Its scoped metric, normed additive group, and normed-space instances supply
the analytic structure used by the real-parameter `HasDerivAt` statements.
The matrix C*-algebra structure comes from that same native scope. No new
matrix type or local replacement norm instance is introduced.

The operator family remains complex-linear. `relaxation_real_apply` proves
the real-to-complex scalar-action bridge entry by entry using
`Complex.real_smul`, `Complex.ofReal_sub`, and `Complex.ofReal_one`;
`relaxation_real_eq` lifts that result by `LinearMap.ext`. Complete positivity
transports the real inequalities with `Complex.zero_le_real`. The real
interval and normalization hypotheses are retained.

## Independent semantic disposition

PASS at source-review level, with finite/conditional/analytic scopes recorded
in `CARNOT_OPERATOR_CONTRACT.md`. The review explicitly checked:

- Noncommutative multiplication order and both commutator defect signs.
- Normalization as a separate condition from positive semidefiniteness.
- Arbitrary finite ancilla types in complete positivity.
- Actual differentiation of the matrix path, with normalization needed to
  express the derivative through the current-state generator.
- Hermitian Hamiltonian and its physical `-I` factor.
- No assumption that the input density commutes with the Hamiltonian.
- Open bath energy exchange retained in the formula.
- No universal system-entropy increase or closed GENERIC conclusion.
- Real finite-step energy parameter, trace-one input, and the entropy-unit
  convention in the explanatory Carnot ledger.

## Reproducible compiler surface

Pinned environment:

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Official Lean archive SHA-256:
  `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`.

Use the maintained scoped checker with the pinned executable and Mathlib clone:

~~~bash
python3 -u tools/quality/check_clifford_dirac.py \
  --mathlib-root "$MATHLIB_ROOT" \
  --lean "$LEAN_BIN" \
  --output verification-replacement-thermal \
  --target InfoGeometry.Quantum.ReplacementRelaxation \
  --target InfoGeometry.Quantum.ReplacementHamiltonian \
  --target InfoGeometry.Quantum.ReplacementGibbs
~~~

Despite its historical filename, this maintained checker accepts the explicit
target list, copies each repository dependency from the current source tree,
serializes compilation under the shared build lock, and invokes the native
declaration axiom audit for the selected owners. Acceptance additionally checks
that all three selected owners have zero compiler warnings; the workflow makes
that check explicit.

The checker records the discovered repository closure and direct Mathlib
roots in its receipt. CI caches only the pinned runtime and dependency
artifacts. It checks the exact PR source head and uses fresh repository
outputs with neither `--incremental` nor `--skip-audit`. The observed module
and declaration counts are recorded with the receipt below.

## Validation recorded before the final warning cleanup

- Independent mathematical and documentation review: passed at source level.
- Pinned dependency cache hydration: passed for the discovered union needed by
  this task and the three older proof repairs; no pins changed.
- Strict placeholder scan of all three new owners: passed.
- Warning-strict semantic-vacuity scan at the receipt source: exit 1,
  exactly four reviewed helper warnings and no error-level findings. The
  individual dispositions remain below.
- Focused workflow: YAML structure and all three embedded Python scripts
  parsed successfully; target and path coverage checked against the maintained
  closure helper.
- Exact-source kernel compilation and declaration axiom audit: **passed** in
  [run 44273533242](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44273533242),
  job `134695804771`, at source head
  `9d03ea978991bb77cd815382bc851eaac28c5d9d`. All 56 repository modules compiled.
  The native audit covered all 74 owned declarations and found only the three
  allowed Lean foundations.
- Selected-owner zero-warning acceptance: **failed** for that same receipt.
  Relaxation and Gibbs each had zero warnings; Hamiltonian had two unused
  `Matrix.mul_smul` simplifier arguments. The workflow failed at this warning
  gate after successful kernel compilation and axiom audit.
- The cleanup removes only those two unused arguments from the Hamiltonian
  `simp` lists; its explicit `rw` uses of `Matrix.mul_smul` remain. Fresh CI for
  the cleanup source was not yet available when this record was prepared.
  Consult the PR checks for its exact-head zero-warning result; the earlier
  receipt is not a zero-warning pass.
- Actual staged pre-commit proof gate: passed for the initial draft and the
  published compiler repairs.
- Root pre-push gate on preserved initial local head
  `40206d2d61ead09e5a870d58e05a4ea6646ebcb2`: completed with exit 1. Its locked
  Lake stage stopped during package loading at the absent
  `external_refs/homotopy-hypothesis-lean4`, before checking the selected
  Lean proofs. The subsequent semantic-content scan completed with exit 2
  because six tracked symlink targets had not been materialized in the local
  checkout. This local coverage failure is separate from the missing Lake
  prerequisite and is not attributed to the upstream source. Restoration
  uses exact HEAD bytes; no post-restoration scan receipt is claimed here.
  These observed exits are not replaced by a scoped-build result.
- Whole-root/default-target acceptance: not established.

The completed native receipt reports:

| Selected owner | Audited owned declarations | Compiler warnings |
| --- | --- | --- |
| `ReplacementRelaxation` | 31 | 0 |
| `ReplacementHamiltonian` | 31 | 2 |
| `ReplacementGibbs` | 12 | 0 |

Receipt artifact ID: `14416365185`. Artifact SHA-256:
`bbcbb541cdf5cab37c6f4fc5538adf603ad7038c99d6df8c1530c35064ced79d`.
This receipt establishes kernel and axiom-audit acceptance for the identified
source bytes. It does not establish warning-strict acceptance or acceptance of
the subsequent cleanup. The PR checks report the latter from its fresh receipt.

## Observed repair history

| Observed attempt | Diagnostic | Current repair and scope |
| --- | --- | --- |
| [Run 44268362538](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44268362538), source `b22b88bc70730f2ad213baede7d91e14a1223c43` | Reserved `λ` binder rejected by the parser; the analytic theorem also lacked `NormedAddCommGroup Mat`. | Parameters use `weight` and `other`; the relaxation owner imports and opens Mathlib's native L² operator-norm scope. The matrix carrier and mathematical hypotheses are retained. |
| [Run 44272095036](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44272095036), source `2bbcef3985083c18afa10e017d7e60b0f018c092` | Real/complex scalar-action goals remained unsolved, and `Complex.ofReal_nonneg` was unavailable in the pinned API. Downstream new owners were blocked by the relaxation failure. | The explicit entrywise scalar bridge and native `Complex.zero_le_real` replace the unsuccessful transport steps. No real interval, normalization, ancillary matrix, or noncommutative-order condition is weakened. |
| [Run 44273533242](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44273533242), source `9d03ea978991bb77cd815382bc851eaac28c5d9d` | All 56 repository modules compiled and all 74 owned declarations passed the native axiom audit. Two unused `Matrix.mul_smul` arguments in Hamiltonian failed the selected-owner warning gate. | Remove those two unused `simp` arguments while retaining the required `rw` uses. The cleanup requires its own exact-source zero-warning receipt in the PR checks. |

## Root prerequisites and unchanged repository-wide blockers

Read-only inspection of the current root configuration distinguishes package
availability from theorem failure:

| Declared path dependency | Observed availability and provenance |
| --- | --- |
| `lib/InfoGeometryCore` | Present as an ordinary tracked source tree with its Lake config and `Basic.lean`; its own Mathlib requirement matches the root pin. The historical local-workstation URL in `.gitmodules` is not needed to use this present tree. |
| `external_refs/homotopy-hypothesis-lean4` | Absent. The path-only manifest entry supplies no Git source/revision, and the current tree and `.gitmodules` contain no corresponding checkout provenance. This is the observed root Lake blocker. |
| `external_refs/atlas-lean` | Absent. The manifest gives a path and config filename, with no tracked tree or submodule source. The historical inventory's short SHA `34ffed3` is not a complete reproducible source specification, as already recorded in `MAIN_VERIFICATION_REPAIR_20261023.md`. |
| `external_refs/gift-framework-core` | Absent but concretely pinned by the gitlink `e6f3c3ac2140c2324fb2ae029c32233e73aa5e92` and `.gitmodules` URL `https://github.com/gift-framework/core.git`. Exact restoration is specified; repository access and nested dependencies have not been tested here. |

No guessed Atlas or HomotopyHypothesis revision, replacement package, dependency
pin change, or stub is part of this PR. The separate `external_refs/GIFT`
repository is not the root Lake package `external_refs/gift-framework-core`.

The previously inspected global CI jobs for source
`2bbcef3985083c18afa10e017d7e60b0f018c092`, against base
`08c34e03f610b452e03422037949196dc7d92d6d`, also recorded the following blockers.
The relevant failure inputs are unchanged by this PR. These are historical
observations; current-head results must be reported separately when available.

| Global check | Observed blocker |
| --- | --- |
| [Reviewed integration checkout](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44272095034) | Git submodule initialization failed because the existing `external_refs/auto-ontology` gitlink has no URL in `.gitmodules`; Lean did not run. |
| [Closure-debt CI](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44272094854) | The unchanged workflow's Python environment lacked `pytest`, before subsequent audits or Lean. |
| [Documentation site](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44272094860) | `actions/configure-pages` received a Pages-site HTTP 404 before dependencies or the build. Site availability versus access was not resolved. |
| [Repository case-sensitivity check](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44272094914) | Existing `lean/docs` and `lean/Docs` paths collide under case-insensitive comparison; the later Lean style check was skipped. |

## Semantic-vacuity warning review

The warning-strict heuristic scan reports four short helper surfaces:

| Declaration | Actual statement | Disposition |
| --- | --- | --- |
| `relaxation_apply` | Evaluation of the newly defined linear map | Definitional API used in the composition, trace, and positivity proofs. |
| `generator_apply` | Evaluation of the combined linear operator | Definitional API used by trace preservation and energy balance. |
| `relaxation_one` | Parameter one yields the identity operator | Endpoint law for the full operator family. |
| `relaxation_of_trace_zero` | Every traceless matrix is scaled by the parameter | Nonempty operator subspace result; no diagonalization assumption. |

These are ordinary helper lemmas, not proof of the stronger thermodynamic
narrative. Their short proofs are retained, and the scan's warning-strict
exit is recorded rather than suppressed or evaded.

## Remaining obligations

A combined Hamiltonian-plus-relaxation trajectory, entropy or relative-entropy
monotonicity, heat-reservoir state, GENERIC degeneracy laws, driven Carnot
strokes/efficiency, reservoir-resolved NESS production, Weyl spacetime gauge,
Gromov–Witten volume, Wilson-loop transport, Goldstone modes, and causal
wavefront dynamics are not established here. The exact next mathematical
requirements are stated in the contract.
