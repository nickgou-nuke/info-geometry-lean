# Real BKM and squared-associator validation

## Source checkpoint: 2026-11-17

Status: **draft; native compilation and declaration axiom acceptance pending**.
A proof source with no placeholders is not an executed kernel check.

Base: `08c34e03f610b452e03422037949196dc7d92d6d` in
`nickgou-nuke/info-geometry-lean`. The independent branch is
`codex/real-bkm-constrained-dissipation-20261117`; it does not depend on the
separate twin-duality draft. The separate Yang--Mills submission snapshot is
unchanged.

Pinned Lean: `leanprover/lean4:v4.34.1`.
Pinned Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
No dependency, root build configuration, maintained gate, or shared lock changes.

## Reviewed source

All six new owners have been read at their actual declared types. Review
covered the spectral density/full-matrix distinction, integral order and
transpose, frame-pullback direction, the two constraint normal equations,
zero denominator boundaries, native kernel/range equalities, exact
commutator preservation, actual matrix-exponential normalization, positive
observer versus indefinite form, ordered associator multiplication, and the
common-kernel separation condition. An independent second review corrected
the documented frame orientation and explicit symmetry assumptions.

The raw inputs are preserved byte for byte with their original names and
SHA-256 values in the intake manifest. Their claims are not acceptance evidence.

| Owner | Source SHA-256 |
|---|---|
| `Canonical.KuboMoriBogoliubovPositiveForm` | `25b179ec4589da107ba58379d3bb3889cc3ef7deac769fdb2b34303f98a3952e` |
| `Thermo.ConstrainedBilinearProjection` | `cee7aea84232415b82b4f4fe013ed67b99481d9be9f843ba2dafe65892846cd5` |
| `Thermo.RealBKMConstrainedForce` | `7384b6574545271dab1721769c2ab9925bc2c7987b1b0cf62216b6ebaa5e4c79` |
| `Thermo.RealBKMGibbsStationarity` | `327359d883592386783e0ca50ab79ec690f478dbe7c1a991ccf146ff16560910` |
| `Thermo.AssociatorGramDissipation` | `73a51a6025bb6d5828fa762cf7a871d8c7af4231bf8c831a49638c2550a69914` |
| `Canonical.SplitOctonionAssociatorGram` | `2638db20e0eeea8a199553e4c50e0ece20bc433b90e06431c1a24dcd00b8cbfd` |

## Source checks actually executed

- Strict maintained placeholder scan on each of the six target owners: exit 0;
  **zero hard findings**, 15 soft notices. These are reviewed section-assumption
  or supporting-proof notices; they are distinct from compiler warnings.
- Maintained semantic-vacuity gate at `--fail-on error`: exit 0; zero errors
  and 19 supporting evaluation/linearity notices. The substantive theorem
  contracts have been inspected separately.
- Maintained closure resolver: **66 repository owners**, including six selected
  targets, and **80 native import roots**. This resolves the exact source graph;
  it is not a compilation result.
- Authored-file whitespace check: passed.
- Installed staged proof gate on the six staged owners: passed. Scalar
  computations in the concrete matrix witness are explicit real-only helpers;
  operator statements preserve the original full matrix carrier.

The first local placeholder invocation could not import `tools.pathing` because
that unchanged helper was excluded from the sparse working view. Materializing
the exact tracked helper resolved the environment issue; all six scans then
ran and passed. The staged gate likewise required materializing the exact
tracked QMS screener, including its original executable mode, before it could
run. Its operator-tactic findings were addressed by native bilinear symmetry
and an explicit real scalar contradiction, then the gate passed. No checker
implementation was modified.

## Native command and acceptance requirements

From the independent checkout:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/44e3088154ac/mathlib4 \
  --lean /workspace/scratch/50ddde16aff2/runtime/lean-4.34.1-linux/bin/lean \
  --output /workspace/scratch/0878f2086cff/verification-real-bkm-associator \
  --incremental \
  --target InfoGeometry.Canonical.KuboMoriBogoliubovPositiveForm \
  --target InfoGeometry.Thermo.ConstrainedBilinearProjection \
  --target InfoGeometry.Thermo.RealBKMConstrainedForce \
  --target InfoGeometry.Thermo.RealBKMGibbsStationarity \
  --target InfoGeometry.Thermo.AssociatorGramDissipation \
  --target InfoGeometry.Canonical.SplitOctonionAssociatorGram
```

A single local compiler owner uses the maintained `/tmp/info-geometry-build.lock`.
The checker copies and hashes the entire source closure, checks the pins and
actual Lean version, compiles every owned dependency, and generates a native
audit for every declaration owned by the six targets, including private and
generated declarations. Acceptance requires `report.status = passed`, zero
compiler warnings in every selected owner, and an axiom union contained in
`propext`, `Classical.choice`, `Quot.sound`.

The focused `Real BKM and associator kernel check` workflow fetches the exact
PR head without recursively traversing unrelated submodules. It resolves the
same closure, fetches only pinned native import caches under the maintained
lock, compiles target source rather than restoring target artifacts, requires
zero new-owner warnings, and uploads the native report, audit source, logs,
semantic report, and evidence hashes. Queueing this workflow is not acceptance.

## Integration and mathematical boundaries

Root integration and scoped native source acceptance are separate. Prior
observed repository-wide jobs on the same base encountered missing external
submodule/path dependencies and a tracked case-collision; this task neither
repairs those unrelated files nor treats a scoped check as a successful root
build or pre-push gate. Current PR-specific job results must be recorded at
their actual source revision.

The spectral BKM construction acts on full real matrices and allows
noncommuting observables. It does not yet construct a spectral decomposition
of an arbitrary positive matrix or prove independence of every eigenbasis.
The split-octonion construction uses the actual full eight-dimensional real
carrier and a positive observer form; it does not change its product into an
associative one. A Gram response and the stationary Gibbs implication do not
supply a density-cone-preserving trajectory, entropy-gradient identification,
Jacobi identity, heat/erasure theorem, or asymptotic convergence. Precise
mathematical statements and corrected input claims are in
`REAL_BKM_ASSOCIATOR_CONTRACT.md`.
