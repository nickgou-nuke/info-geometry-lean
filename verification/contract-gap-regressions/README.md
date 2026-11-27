# Contract gap regressions

## Status

**Elaborated diagnostic candidate; draft review material.** The focused Lean file check passes. The
owner-closure axiom audit and publication route remain incomplete.

This directory accompanies the [semantic contract gap audit](../../docs/SEMANTIC_CONTRACT_GAP_AUDIT_2026-11-26.md).
It does not modify a canonical owner, the Lake target graph, dependency pins, or a quality gate.
The existing declarations are imported without changing their carriers or definitions.

- Reviewed main: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
- Lean pin: `leanprover/lean4:v4.34.1`.
- Mathlib pin: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Candidate SHA-256: `3fbc1750ab285f1fc7097df6e8a2151fdb754f2d7e863fff274747fd18a8b981`.
- Candidate size: 9,226 bytes.

The [historical roadmap in PR #466](https://github.com/nickgou-nuke/info-geometry-lean/pull/466)
is complementary. This directory adds the concrete diagnostic scripts and their exact validation
boundary; it does not claim to close the roadmap's mathematical gaps.

## Theorem contract

All candidate declarations are in `InfoGeometry.GapRegression`.

| Declaration | Exact intended result | Boundary |
|---|---|---|
| `columnBalancedExample_colLyapunov_increases` | The owner-defined absolute column residual increases from `0` to `2/15` after a row step on the specified positive 2 by 2 matrix | Does not refute the phase-aligned inequality or classical Sinkhorn convergence |
| `not_fixedColumnResidual_descent` | Positive row masses alone do not imply fixed-column-residual descent | A support-dependent convergence theorem remains a separate target |
| `columnBalancedExample_phase_residuals` | The existing phase-aligned before/after residuals are both zero for the example | Preserves the precise existing normalization statement |
| `scalarNilpotentLadder_isEmpty` | The legacy real-scalar `PeirceLadder.NilpotentLadder` type is empty | Does not apply to operator or Clifford CAR models |
| `rankOne_commutator_expectation_pos` | The stated ordered rank-one commutator has positive expectation at a nonzero vector orthogonal to the second nonzero vector | Uses the native positive real inner product; no finite-dimensional assumption |
| `kms_commutatorOrthogonal_iff_zero` | The exact owner predicate over all bounded real endomorphisms holds iff the vector is zero | Does not address a restricted represented observable algebra |
| `kmsStructuralWitness_isEmpty` | The exact structural witness has no inhabitant | Does not assert that Lean is inconsistent or refute analytic KMS states |

The KMS specialization reuses the owner's `DoubledSpace`, `AlgebraEnd`, `clockAxis`, phase norm
identity, and phase skewness identity. No scalar complex unit or commuting surrogate is introduced.

The approximate-KMS homogeneity obstruction, modular sign, core trace, and weight issues are
mathematical arguments in the companion audit. They are not newly formalized by this file.

## Source review and checks performed

Independent source review checked the exact owner definitions and the pinned Mathlib APIs. During
publication review, one explicit `real_inner_comm` rewrite was oriented correctly so that the
skewness identity is expressed in the same inner-product order as the orthogonality goal. The
current source uses nondeprecated continuous-linear-map application lemmas and has no warnings in
its focused elaboration check.

The prior saved candidate had SHA-256
`d0424bcc97fe5ecf6b00c479d4d82c8e6be4fc4e26bddeeceed34ef1a9ded92c`.
It was recovered with that checksum. The current publication corrections orient the rewrite and
use current application lemmas without unnecessary simp rules.

| Check | Observed result |
|---|---|
| Exact rational arithmetic (`fractions.Fraction`) | Passed: column sums `(1,1)` become `(14/15,16/15)`; absolute residual `0` becomes `2/15` |
| Source token scan | No occurrences of `sorry`, `admit`, custom `axiom`, `native_decide`, or `unsafe` in the candidate |
| `python3 tools/quality/semantic_vacuity_gate.py verification/contract-gap-regressions/GapRegression.lean --fail-on error` | Exit `0`; zero findings on this file |
| Independent semantic/API review | Completed; does not substitute for elaboration |
| Current candidate check: `python3 tools/infra/run_locked_lean.py verification/contract-gap-regressions/GapRegression.lean` | Passed after source cleanup; no warnings |
| Candidate native axiom audit | Not run |
| Staged proof gate and diff check | Passed: `proof_proxy_staged_gate: ok` and `git diff --cached --check`; the normal local commit also ran the installed pre-commit hook |
| Pre-push publication gate | Exit `2`: the isolated candidate has no package-specific build route in the root gate |

The exact source-closure command attempted from the repository root was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/794b42c200b9/mathlib \
  --output /workspace/scratch/9774d79a92d1/validation/owner-closure \
  --target InfoGeometry.Canonical.SinkhornFoundation \
  --target InfoGeometry.Canonical.KMSSinkhornSeedState \
  --target InfoGeometry.Canonical.TomitaTakesaki \
  --target InfoGeometry.Peirce.PeirceLadderOperators
```

The maintained checker verified the pinned Mathlib revision and clean tracked source, found a
closure of 50 repository modules, copied that closure to its isolated output, and printed
`Waiting for shared build lock`. The occupied shared lane was left intact. This waiting Python
invocation was interrupted with exit `130`; no `CHECK` result or compiled module was produced.
No running Lake or Lean process was terminated. The toolchain executable is installed in this
publication workspace; the earlier audit's missing-toolchain observation belongs to its prior
workspace and is not this attempt's result.

That earlier source-closure attempt also reported missing imported artifacts in its isolated
validation workspace. The current focused candidate check succeeds using the checkout's existing
Lean environment; the owner-closure audit still needs a complete pinned Mathlib cache layout.

The installed pre-push hook was invoked with the exact local branch/ref update against an absent
remote branch. At checkpoint `a8806531268f1a44fc8b629f20cfe5fcf02d27db`, it classified the range
from the reviewed main and stopped with:

```text
Lean source changes fall outside the package targets routed by this root gate:
  - verification/contract-gap-regressions/GapRegression.lean
Add an explicit locked build route or run the owning package's dedicated gate;
refusing to skip compilation.
```

The root build and later full-gate checks were not reached. No gate, hook, source owner, toolchain,
or dependency configuration was changed. The upstream draft makes the diagnostic source and its
failed publication-gate result reviewable; it is not ready for promotion or merge.

## Remaining acceptance work

1. Compile the exact owner source closure using the maintained checker and a complete pinned
   Mathlib cache. The focused candidate check imports existing compiled owners; it does not rebuild
   that source closure.
2. Run `reviewed_audit_source.audit_source(["GapRegression"])` on the candidate and reconcile all
   owned declarations using `parse_audit_output`. Permit only the repository's stated foundational
   axioms.
3. Resolve the dedicated publication/build route and all required integration gates before
   promoting declarations into focused canonical owners.

Publication for review is not a passing integration gate, a whole-repository build certificate,
or an axiom certificate. Mathematical scope, source review, compilation, and axiom inspection
remain separate evidence.
