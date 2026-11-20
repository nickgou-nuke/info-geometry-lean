# Independent QA-A acceptance: chiral reciprocity

## Disposition

**ACCEPTED_WITH_LIMITED_SCOPE.** The exact three new owners pass independent fresh native compilation, exhaustive native axiom auditing of their owned declarations, strict source checks, and static Gate4. The eight-module repository closure compiled successfully. Root dependency availability remains blocked, and this receipt does not certify `InfoGeometry.All`, a whole-repository build, or the later publication hooks.

Recorded: 2026-11-16T18:43:41.315722+00:00. Base HEAD: `08c34e03f610b452e03422037949196dc7d92d6d`. Branch: `codex/chiral-reciprocity-20261116`. The checked snapshot is staged and uncommitted; its exact worktree/index hashes below identify the accepted theorem content. QA authored no Lean source and made no repository source, documentation, gate, hook, or pin edits.

The completed source inventory is **20 theorem declarations and one definition**. Native ownership auditing measured **33 declarations**, including **12 generated declarations**. These counts describe different surfaces and must not be conflated.

## Results

| Check | Actual result |
|---|---|
| Strict placeholder audit | Three serial explicit-file invocations, exit 0 each; each scanned one file; zero hard, soft, or advisory findings. |
| Semantic vacuity | Exit 0 at `--fail-on error`; complete 3/3 coverage, no read failures; one reviewed definitional-readout warning. |
| Strict OpenGauss screener | Final attempt exit 0; zero violations. |
| Strict OpenGauss refutation | Exit 0; all three owners `PASS`, zero errors or warnings. |
| Fresh maintained kernel check | Exit 0; eight modules compiled with `reused: false`; no `--incremental` or `--skip-audit`. |
| Native declaration axiom audit | Exit 0, zero warnings; 33 owned declarations; axiom union exactly `propext`, `Classical.choice`, `Quot.sound`. |
| Static Gate4 | Exit 0; all three `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`; zero sorries, admits, traps, scope warnings, or index-churn caveats. |
| Root path-package preflight | Exit 1; Atlas/HomotopyHypothesis missing and GIFT uninitialized; InfoGeometryCore passes. |
| Runtime fingerprint | Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`; Lake `5.0.0-src+5045d00`; pinned Mathlib unchanged and clean. |
| Final reconciliation | Exit 0; six task files match index/freeze, eight compiled source hashes match, 17 helper/pin files match freeze and HEAD; `git diff --check HEAD` passes. |

Static Gate4 internally invoked the maintained staged proof gate once per reviewed owner. Its successful result means those internal invocations returned successfully; it emitted no `QMS_STAGED_HOOK` or `QMS_STAGED_HOOK_RACY` finding. The tool does not export successful child stdout. This is separate from executing the actual Git pre-commit hook on the later commit. Static Gate4 correctly retains `kernel_checked: false`; the independent maintained native run supplies the kernel evidence.

## Exact native command and environment

Working directory: `/workspace/scratch/9eb3301f34a1/info-geometry-lean`.

```bash
python3 -B tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/64554963d837/mathlib-4.34.1 \
  --lean /workspace/scratch/64554963d837/lean-runtime/bin/lean \
  --output /workspace/scratch/9eb3301f34a1/reciprocity/final-validation \
  --target InfoGeometry.Analysis.HilbertGramReciprocity \
  --target InfoGeometry.Analysis.HilbertGramMoorePenrose \
  --target InfoGeometry.Analysis.GradedExponentialTrace
```

The checker used the maintained shared build lock, copied the exact repository source closure to a fresh output tree, verified the runtime and pinned Mathlib revision, and rechecked source/helper stability at completion. The initial external lock wait is recorded in raw evidence; no lock alteration or process termination was used. The completed native report is `native-report.json`, and the axiom output is `native-axioms.log`.

Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`. Toolchain: `leanprover/lean4:v4.34.1`. Available pinned Mathlib artifacts were used; this is not a fresh rebuild of all Mathlib.

| Compiled module | Exit | Warnings | Reused |
|---|---:|---:|---|
| `InfoGeometry.Algebra.FiniteSpinAlgebra` | 0 | 0 | No |
| `InfoGeometry.OperatorAlgebra.PartnerEigenspaces` | 0 | 0 | No |
| `InfoGeometry.Analysis.HilbertGramDuality` | 0 | 0 | No |
| `InfoGeometry.Analysis.HilbertGramReciprocity` | 0 | 0 | No |
| `InfoGeometry.Singular.MoorePenrose` | 0 | 14 | No |
| `InfoGeometry.Analysis.HilbertGramMoorePenrose` | 0 | 0 | No |
| `InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace` | 0 | 0 | No |
| `InfoGeometry.Analysis.GradedExponentialTrace` | 0 | 0 | No |

The checker only automatically treats warnings as fatal for its historical CliffordDirac prefix. QA therefore independently inspected every selected-owner warning count; all three are zero. The 14 inherited warnings belong exclusively to unchanged `Singular.MoorePenrose`: 12 deprecated orthogonal-projection API uses and two `haveI` style suggestions. They were not suppressed or repaired in this task. Their exact lines and text are preserved in `qa-acceptance.json` and `dependency-warnings.log`.

## Native audit scope

| Owner | Source theorems | Source definitions | Native owned declarations |
|---|---:|---:|---:|
| `HilbertGramReciprocity` | 5 | 1 | 16 |
| `HilbertGramMoorePenrose` | 7 | 0 | 7 |
| `GradedExponentialTrace` | 8 | 0 | 10 |
| Total | 20 | 1 | 33 |

The maintained generated audit imports the three exact owners and uses native `Lean.collectAxioms` on every constant owned by those modules. It includes generated proof/equation/simplifier declarations, rejects unsafe/partial declarations, and rejects any axiom outside the permitted three-name foundation set. Its log records every audited declaration, module totals, and the combined axiom union; it is not a per-declaration origin trace or an audit of every declaration in every dependency module.

The permitted axioms are ordinary Lean/Mathlib extensionality, classical-choice, and quotient foundations. The reviewed Hilbert and inverse constructions use native noncomputable APIs with their hypotheses exposed. No local axiom, proof hole, oracle, scalar surrogate for operator multiplication, or stored desired conclusion was introduced. The source inspections and independent A-A chain establish mathematical scope separately from these compiler checks.

The generated audit Lean probe stays outside the repository/publication packet. Its SHA256 is `dafbee93aa1105735e89b8e050780af063d290c1c96d40163bde29f322b5f90a`. Maintained generator/helper hashes appear in the native report and acceptance JSON, so the probe can be regenerated without expanding the theorem-bearing source diff.

## Source and hypothesis review

**HilbertGramReciprocity.** The carrier is an arbitrary pair of complete RCLike Hilbert spaces with a bounded continuous linear map. Positivity is derived from an actual `HasEigenvalue` witness and its nonzero eigenvector. The native `LinearIsometryEquiv` normalizes the existing Gram equivalence and proves inner-product preservation. The inverse has the same inverse-square-root normalization of the adjoint. A specified positive parameter may have zero eigenspaces; the construction does not assert eigenvector existence or a complete spectral decomposition.

**HilbertGramMoorePenrose.** All products are typed compositions between the original Hilbert spaces. The absorption identity uses only the inner-inverse law and self-adjointness of `BA`; operator order is retained under adjoint reversal. General eigenspace formulas consume the existing four-equation Moore–Penrose predicate. Closed-range specializations consume the existing constructed bounded inverse, which uses the kernel complement and range projection. The quantitative norm bound cancels a norm proved positive from an actual nonzero eigenvector. Arbitrarily small actual positive Gram eigenvalues then obstruct closed range. This is one-way and does not construct an eigenbasis, an unbounded inverse, or a Fredholm index.

**GradedExponentialTrace.** The general algebraic cancellation reuses the existing cyclic-trace owner. The analytic theorem has an actual complete normed algebra, a continuous linear cyclic functional, and native convergent exponential `HasSum`; it does not replace convergence by a formal symbol. The rectangular corollary constructs genuine doubled blocks and retains arbitrary ordered rectangular products and empty finite index types. The separate commutator cancellation needs only one square-zero factor and an additive cyclic functional; completeness is explicitly omitted for that commutation argument. The explicit 2×2 witness proves noncommutation and distinguishes the anticommutator-exponential weight from the different finite `EF` weight.

The reused owners were read at their definitions, hypotheses and proofs. No claim is made that historical modules merely cited in the explanatory report were all recompiled. Global spectral, unbounded heat, trace-class, APS/eta, boundary-flux and infinity-sector conclusions remain outside this certificate.

## Advisory and CAPA closure

The semantic scanner reports `normalizedGramEigenspaceEquiv_apply` as a `trivial_surface` because its proof is `rfl`. This is a legitimate definitional readout of the forward action of an independently constructed native isometric equivalence. It does not substitute for construction or norm-preservation proof. The warning is retained and adjudicated, not hidden.

Attempt 1 stopped before compilation at strict OpenGauss screening, exit 1, on five T16 scalar-tactic findings. Source inspection showed scalar field/real goals after inner-product or norm projection. The author nevertheless repaired their presentation with explicit scalar algebra/order lemmas, preserving theorem statements and hypotheses. Independent A-A reviewed that delta; all strict source gates and the fresh native run subsequently passed. No gate implementation, pattern, filter, dependency, or pin changed. Original findings, source hashes, commands, and closure evidence are preserved in `capa-history.json` and the full raw evidence.

## Frozen source hashes and integration

| Artifact | SHA256 |
|---|---|
| `lean/InfoGeometry/Analysis/HilbertGramReciprocity.lean` | `64975ff850e1e32ac98e07a52c2d315e83dcc98a0c60833a854bcbd7d7ddbae9` |
| `lean/InfoGeometry/Analysis/HilbertGramMoorePenrose.lean` | `aa016bd2a2711ba481373d23496f3e115e84602c0b4321a3e7731ecc219b1f30` |
| `lean/InfoGeometry/Analysis/GradedExponentialTrace.lean` | `cdde658faa0d10ab862a648062b405c3178eeff0a504bfd0a1be223ccdef3451` |
| `docs/CHIRAL_RECIPROCITY_CONTRACT.md` | `0594dfd47f6ba9a253a4d4f0cf1ce1a5f8ad6c27d49ed146a963274f4d565328` |
| `docs/CHIRAL_RECIPROCITY_FORMALIZATION.md` | `d4ce080275e295eb34152f00f23759d2ced56abae5648d3e664383fedfb6effa` |
| `lean/InfoGeometry/All.lean` | `5bd6c78068eab621d0ba45fc64a5f1da9ba7172295a2ab3fddf69a469537d09f` |

The final worktree and index match those hashes. The five pre-existing modules in the compiled closure also match HEAD. The only `All.lean` change is the three import additions for the selected owners. An independent checkout and real Lake roots were observed; the installed hook path is `.githooks`.

The repository report above still has its frozen development-status text. A separate documentation-only candidate has been reviewed by A-A; the parent will integrate that formatting/qualified explanatory example and actual validation prose after QA release. That does not change these theorem source hashes. The documentation-only receipt is included as a separate review, not as proof of repository integration.

## Root integration and publication limitations

The exact root preflight command was:

```bash
python3 -B tools/infra/ci_bootstrap.py paths --root . \
  --report /workspace/scratch/9eb3301f34a1/reciprocity/qa-evidence/root-path-preflight.json
```

It returned 1. `HomotopyHypothesis` and `Atlas` have missing directories/configuration and untracked path-dependency provenance. `GIFT` is an uninitialized gitlink at `e6f3c3ac2140c2324fb2ae029c32233e73aa5e92` with no required configuration. `InfoGeometryCore` passes. This measures direct package availability/provenance, not compilation or transitive correctness.

QA did not execute the whole root build, actual Git commit hook, or pre-push/post-build publication path. Those later outcomes must be reported separately by the parent. The installed pre-push route requires the exact committed source/worktree relationship and invokes the maintained post-build gate. Since `All.lean` changes, the incremental route includes `InfoGeometry.All`; the selected-owner certificate cannot replace it. The no-argument post-build invocation defaults to incremental even though the hook prints a full-root message. No hook or gate was changed or bypassed.

The scoped mathematical acceptance therefore coexists with blocked root-package eligibility. It is not a whole-repository, `InfoGeometry.All`, or publication-gate pass, and it is not merge approval.

## Independent review chain and evidence

- `aa-source-review.md`: `4bc63e5413fe42394b2fdb545e51695b54bd8cbb1277f94d27ff68f4b770e459` (independent mathematical/source review).
- `aa-source-delta-review.md`: `ade9a8d22b075d5b3b7595ba049c45e4e33e3748bb64f14413d2f41ff9b57b9a` (independent mathematical/source review).
- `aa-source-delta-final.md`: `f46be5933c5587eddb64b47b0d7fb179a24552c3774ae70d112563e22608121a` (independent mathematical/source review).
- `aa-source-t16-review.md`: `a778557a7e79b867d572021a4a9040e577456d5b6aab80b489e1483da52ba555` (independent mathematical/source review).
- `aa-doc-delta-review.md`: `8d4940a1fb8bd362dba6a73a5c7fdf50aac1a95cb9175ad66337be6185a80a87` (documentation-only external candidate review).

`command-ledger.json` preserves exact argv, working directory, timestamps, exit codes, and stdout/stderr hashes for both attempts. `source-gate-receipts.json` preserves all final scanner/static outcomes. `source-index-fingerprint.json` contains the final Git reads, source/index/helper/pin comparisons, and exact All diff. `checksums.json` hashes the publication packet. The verifier's original `native-evidence-sha256.json` retains its raw-run evidence hashes; referenced binaries, per-module raw logs, and the generated Lean probe remain outside the packet.

**All assigned QA validation processes completed. The build/test lane is released with delivery of this receipt.**
