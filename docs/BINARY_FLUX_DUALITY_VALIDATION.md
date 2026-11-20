# Binary flux validation record

Date: 2026-11-20. Base revision:
`586c14bc9fb94eb09b56f7dc850d9d5297269f91`.

**Focused mathematical verification passed. Root-package integration is
blocked before target elaboration.** These are separate outcomes.

## Exact checked source

| Owner | SHA-256 | Owned declarations audited |
|---|---|---:|
| `lean/InfoGeometry/Algebra/BinaryFluxProjectors.lean` | `678455ad82d277f9c0400d045f9090e4e67db385fc69f3a130c98fbdac4e540c` | 43 |
| `lean/InfoGeometry/Algebra/BinaryFluxDuality.lean` | `8f942501f927f6ada9a3e879f85944e8c727f3a513a3d19c7de5d3ea0645e692` | 25 |

Runtime: official Lean **4.34.1**, Lean commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and clean Mathlib checkout at the
unchanged repository pin `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The official runtime archive checksum and all eight Mathlib package revisions
were checked. No root pin, checker, gate, or Lake configuration was changed.

## Decisive checks

The maintained `tools/quality/check_clifford_dirac.py` checker accepts explicit
target modules despite its historical filename. It copies the exact repository
source closure, verifies the runtime and Mathlib pins, acquires the maintained
shared build lock, compiles that closure, checks source hashes again, and
audits every declaration owned by the selected modules. The ownership check
includes private and compiler-generated declarations.

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /path/to/clean/pinned/mathlib4 \
  --lean /path/to/lean-4.34.1/bin/lean \
  --output /path/to/fresh/binary-flux-check \
  --target InfoGeometry.Algebra.BinaryFluxProjectors \
  --target InfoGeometry.Algebra.BinaryFluxDuality
```

This command was run independently into fresh output after the final proof
repair. All six modules compiled with **exit 0 and zero warnings**:

1. `InfoGeometry.Algebra.FiniteSpinAlgebra`
2. `InfoGeometry.Algebra.NoncommutativePlaneWaveKernel`
3. `InfoGeometry.Algebra.FiniteGroupFourier`
4. `InfoGeometry.LLM.WalshCharacterGeometry`
5. `InfoGeometry.Algebra.BinaryFluxProjectors`
6. `InfoGeometry.Algebra.BinaryFluxDuality`

The native audit passed for **68 owned declarations**. The complete observed
axiom set was `propext`, `Classical.choice`, and `Quot.sound`. No unsafe,
partial, custom-axiom, or proof-hole dependency was accepted. The focused
checker was not run with `--skip-audit` or incremental reuse for acceptance.

| Additional check | Result |
|---|---|
| Maintained locked individual-file elaboration | Both owners passed |
| `proof_proxy_staged_gate.py --strict` on both owners | Exit 0 |
| `axiom_audit.py --fail-on-gaps` on both owners | Exit 0 |
| `semantic_content_audit.py --gate-review` on both exact file prefixes | Exit 0; no findings |
| `semantic_vacuity_gate.py` at its normal error threshold | Exit 0; five reviewed helper warnings |
| The same semantic-vacuity scan with `--fail-on warning` | Exit 1; the same five warnings, no error findings |
| `scripts/vacuity-linter.py <owner> --json` | Exit 0; three reviewed lexical flags in Projectors, none in Duality |
| `git diff --cached --check` | Exit 0 |

## Independent semantic review and corrective action

Generation, source audit, and acceptance checks were performed by distinct
agents. The independent source auditor returned **PASS** for the two owner
hashes above. The finite convolution, arbitrary-algebra product ordering,
charge transport, Fourier inversion, transpose covariance, longitudinal
projection, and both normalizations were inspected directly.

An initial strict-source check flagged `ring` at the final scalar step of
`fluxDuality_apply` as an operator-tactic misuse. The goal had already been
expanded to a product of three real scalars. Replacing that tactic with the
explicit scalar theorem `mul_right_comm` resolved the finding. The final
source passed fresh compilation, native auditing, strict scanning, and
independent source re-review. No scanner rule was modified or disabled.

The five semantic-vacuity warnings identify `character_apply`,
`projector_eq_average`, `projector_idempotent`, `projector_orthogonal`, and
`longitudinalProjection_transpose_covariant`. They are accurate definitional
helpers or corollaries of the constructed transform, proved convolution law,
or supplied pointwise covariance. The independent auditor inspected their
actual dependencies and consumers and found no semantic vacuity. The stricter
warning-threshold command's nonzero result is retained in the table above.

The simple linter's three flags arose from line-based parsing: a term proof
continued on the next line; a local simplification proved the zero-character
identity; and a parameter was used in a later proof line. They do not identify
an empty proof or an unused mathematical hypothesis in the actual source.

## Root integration and publication boundary

The genuine root Lake executable, with the unchanged repository configuration,
was invoked through the maintained wrapper:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --wfail \
  InfoGeometry.Algebra.BinaryFluxProjectors \
  InfoGeometry.Algebra.BinaryFluxDuality
```

It fetched the exact root-pinned Mathlib and LeanCopilot revisions, then exited
**1**, before target elaboration:

```text
error: HomotopyHypothesis: package directory not found:
  .../external_refs/homotopy-hypothesis-lean4
```

The independent path-package preflight also found missing/untracked package
configuration for `Atlas` and an uninitialized pinned `GIFT` gitlink. These
dependencies were not replaced with stubs or unpinned checkouts. The verified
focused source closure does not repair or certify the root package.

The publication gate must be reported at its actual outcome. This document
does not authorize bypassing a failed gate or claim a successful whole-root
build. The remaining mathematical boundaries are recorded in
[the theorem contract](BINARY_FLUX_DUALITY_CONTRACT.md).
