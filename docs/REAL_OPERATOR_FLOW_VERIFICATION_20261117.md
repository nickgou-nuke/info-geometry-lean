# Real operator exponential bounds: verification

## Result and scope

On 2026-11-17, the four new owners passed the pinned native Lean compiler and
the maintained complete declaration axiom audit. Their exact repository import
closure contains **62 Lean modules**. All four new
owners have **zero compiler warnings**. Independent semantic review and ten
scoped source-analysis commands also passed on the exact same source hashes.

This is acceptance of the selected theorem sources and their declaration
dependencies. Root Lake integration and the repository's pre-push gate are
separate checks. The recorded root path-package preflight failed as described
below; this document makes no whole-repository build or publication claim.
The delivery record and PR description record the final commit, tree, hook
outcomes, and publication status without embedding a self-referential commit
hash in this source document.

## Exact source and runtime identity

- Upstream baseline: `08c34e03f610b452e03422037949196dc7d92d6d`.
- Branch: `codex/real-loxodromic-flow-20261117`.
- Lean toolchain: `leanprover/lean4:v4.34.1`.
- Observed runtime: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.
- Mathlib commit: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The native checker confirmed the repository pins, matching runtime, clean
pinned Mathlib source, the complete copied repository source closure, and
unchanged source/helper hashes at completion. The following owner hashes also
match the staged source analyses and independent final source review. Paths
are relative to `lean/InfoGeometry/OperatorAlgebra/`.

Native verification ran on the staged candidate before its source commit was
created. The final delivery checks bind every source in the verified closure
to the immutable committed bytes; the report's original `local_revision`
continues to identify the pre-commit checkout baseline.

| Owner | SHA-256 |
| --- | --- |
| `ExponentialGradeBounds.lean` | `47a787cafc21a98e6fbc349b0b4dde5d8d18f287c301eb45ad78102f3ca6c09c` |
| `QuadraticExponentialBounds.lean` | `d8e70168ac4ada9103acfb86da3a7992f5c9dd61117e876b3efeb2b649b67127` |
| `TripotentExponentialBounds.lean` | `91efaa0d2396f19f5f16a07e773f74375021724de9b1acaea785b694a2157622` |
| `LoxodromicExponentialBounds.lean` | `879b0187c70abd5b2ef48dd84810c21faf11fa9be6c9f4e726c0d0bf7b6a76f8` |

## Exact mathematical scope

The carrier is an arbitrary complete normed associative real algebra. Its
multiplication, norm, `NormedSpace.exp`, and existing exponential conjugation
are retained. All boundedness statements quantify over **every real time**.
The convention is `expTransport H X t = exp(t • H) * X * exp(t • (-H))`.

| Owner / principal theorem | Proved conclusion and essential hypotheses |
| --- | --- |
| `ExponentialGradeBounds.expTransport_eq_exp_smul_of_lie_eq` | `H*X-X*H = rate•X` gives transport `Real.exp (rate*t) • X`, its exact norm, and boundedness iff `rate=0 ∨ X=0`. Contraction iff `rate*t≤0` additionally requires `X≠0`. |
| `QuadraticExponentialBounds.bddAbove_norm_exp_iff_of_sq_eq_scalar` | Under `[Nontrivial A]` and `G^2=q•1`, the exponential norm is bounded iff `q<0 ∨ G=0`. For `G^2=-(r^2)•1`, `r>0` gives bound `‖1‖+‖G‖/r`; `r≠0` gives period `2*pi/r`. |
| `QuadraticExponentialBounds.bddAbove_norm_exp_mixed_iff` | With `[Nontrivial A]`, `I^2=-1`, `K^2=1`, and `I*K=-(K*I)`, boundedness for `θ•I+η•K` is equivalent to `η^2<θ^2 ∨ θ•I+η•K=0`. |
| `TripotentExponentialBounds.bounded_expTransport_iff_commute` | `S*S*S=S` gives boundedness of the full orbit of `X` iff `Commute S X`, using the native continuous five-grade projectors. |
| `LoxodromicExponentialBounds.bounded_loxodromic_expTransport_iff` | `S*S*S=S`, `J^2=-1`, `Commute S J`, and `γ≠0` give boundedness under `γ•S+ω•J` iff `Commute S X`; `ω` is arbitrary and `X` need not commute with `J`. |
| `LoxodromicExponentialBounds.expTransport_add_scalar_one` | Adding `c•1` to any generator leaves its actual conjugation orbit unchanged. |

The quadratic zero-generator exception is explicit. No commutativity of the
ambient algebra, finite dimension, Hilbert adjoint, or normalized unit norm is
assumed. The more general commuting-factor lemma assumes a bound on the rotary
factor, not on the orbit it is intended to classify; the loxodromic theorem
derives that factor bound from `J^2=-1`.

These statements do not construct a modular/KMS state, Hardy space, irreversible
semigroup, or physical stability interpretation. Projective coordinate bounds
are not used as substitutes for norm bounds. The full claim contract is
`docs/REAL_OPERATOR_FLOW_CONTRACT_20261117.md`.

## Native compilation and axiom audit

The final incremental run exited **0**, with report status **`passed`**.
It compiled **3** modules and reused **59** successful module
artifacts after verifying their exact source/dependency fingerprints and
artifact hashes. All 62 modules passed; none was failed or blocked.

| New owner | Compiler exit | Warnings | Audited declarations |
| --- | --- | --- | --- |
| `ExponentialGradeBounds` | 0 | 0 | 5 |
| `QuadraticExponentialBounds` | 0 | 0 | 11 |
| `TripotentExponentialBounds` | 0 | 0 | 9 |
| `LoxodromicExponentialBounds` | 0 | 0 | 10 |

The generated native audit covered **35 declarations** owned by the four
modules, including private and generated declarations. It rejected unsafe or
partial declarations and any transitive axiom outside the permitted set.
The observed axiom output was `[propext, Classical.choice, Quot.sound]`.
There are no admitted proofs or additional custom axioms in the accepted
declaration dependencies.

The imported owners retain **165 existing compiler warnings**,
recorded in their module logs; no unrelated owner was edited to suppress them.
The maintained script's historical automatic warning-failure prefix is
`InfoGeometry.OperatorAlgebra.CliffordDirac`. For these custom targets, the
four warning counts above were therefore checked explicitly before acceptance.

The review bundle contains the final `report.json`, `axioms.log`, generated
`CliffordDiracAudit.lean`, module logs, environment record, exact invocation
record, and evidence manifest under `evidence/`. The generated audit is evidence
and is not counted as one of the 62 repository source modules.

### Recorded native command

Run from `/workspace/scratch/d8c17edeea4e/real-flow-lean`, using the maintained
shared-lock checker and the already initialized pinned Mathlib checkout:

```bash
python3 -u tools/quality/check_clifford_dirac.py --mathlib-root /workspace/scratch/44e3088154ac/mathlib4 --lean /workspace/scratch/50ddde16aff2/runtime/lean-4.34.1-linux/bin/lean --output /workspace/scratch/d8c17edeea4e/real-flow-native --incremental --target InfoGeometry.OperatorAlgebra.ExponentialGradeBounds --target InfoGeometry.OperatorAlgebra.QuadraticExponentialBounds --target InfoGeometry.OperatorAlgebra.TripotentExponentialBounds --target InfoGeometry.OperatorAlgebra.LoxodromicExponentialBounds
```

### Initial failures and repairs

The first run compiled all 58 existing dependencies, but the original
`ExponentialGradeBounds` and `QuadraticExponentialBounds` scripts failed.
The two dependent new owners were blocked and no axiom audit was reached.
That failed report, original source hashes, and logs are preserved separately
under `evidence/history/run-1/` in the review bundle.

The reviewed repairs used an explicit constant-multiplication derivative and
function-form scalar-product derivative with `convert!`, exposed the periodicity
equality before rewriting, and replaced redundant scalar-division tactics with
direct cancellation identities. No theorem signature, carrier, hypothesis, or
conclusion changed. The final native result above applies to the repaired
hashes, not the original failed snapshot.

Run 2 compiled both repaired owners, reported two proof-syntax warnings in
the eigenoperator owner, and identified that the tripotent owner's local
rational scalar structure depends on Mathlib's noncomputable real normed field.
The loxodromic owner remained dependency-blocked in that run. The next repairs
removed the unused simplifier argument and unnecessary tactic separator and
added a standard `noncomputable section` annotation to the tripotent and
loxodromic owners with the same local scalar structure. These annotations do
not change theorem types or introduce axioms. The review and final native run
cover all repairs. Intermediate evidence is retained under its original run
number and source hashes.

## Refreshed source evidence

The ten commands recorded in `real-flow-qa-gates.json` completed after all
final repairs were integrated. Each record includes its exact arguments,
working directory, source hashes, exit code, and log. All ten statuses are
`passed`; none of these commands invokes Lean, Lake, or the kernel. Exact
commands appear below. Detailed timing remains in the command records.

| Check | Recorded result |
| --- | --- |
| Scoped semantic-content audit | Exit 0; four files selected and read; complete coverage; zero findings. Its authority is lexical analysis, not a mathematical proof. |
| Staged proof-proxy | Exit 0; the four staged owners passed. This is not the complete pre-commit hook. |
| Four strict placeholder audits | Each exit 0; zero hard findings. One soft `skeletal-proof` finding remains on the loxodromic normalization lemma; the other owners have no findings. |
| Semantic-vacuity gate (`--fail-on error`) | Exit 0; four files read; one `trivial_surface` warning on the same lemma; no error findings. |
| Strict OpenGauss refute | Exit 0; all four owners `PASS`, with zero traps or warnings. |
| OpenGauss GATE_4 source review | Exit 0; all four `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`; `kernel_checked=false`, `custom_axioms=null`. No kernel check was requested. |
| Debt-token source scan | Exit 1, the recorded expected result for no matches in the four owners. |

The scoped reports are `real-flow-qa-semantic-content.{json,md}`,
`real-flow-qa-placeholder-<Owner>.json`, and
`real-flow-qa-semantic-vacuity.json`. The staged-check, refute, and GATE_4
outputs are preserved in their corresponding command logs. The earlier,
pre-repair source-analysis records are retained separately under
`real-flow-native-history/source-qa-initial/`.

Both remaining heuristic flags concern `expTransport_smul_generator`.
Independent semantic review accepted it as a useful normalization lemma:
scalar associativity and negation identify generator scaling with time
reparametrization of the existing exponential conjugation. The observable and
noncommutative multiplication order are retained. Its boundedness corollary
uses inverse time substitution under the explicit nonzero-scalar hypothesis.
The flags remain recorded; no code was changed merely to suppress them.

The final entry in `real-flow-source-review.json` accepts the current four
hashes after the repairs. It confirms that theorem signatures and hypotheses
are unchanged, the integrating factor derives the exact flow, native bounded
Peirce projections prevent cancellation of growing components, and the
loxodromic theorem derives its rotary-factor bound from `J^2=-1` while
preserving the inverse-factor order. The contract explicitly includes the
tripotency hypothesis already present in the loxodromic theorem.

Earlier pinned-API reviews did not detect the elaboration failures subsequently
reported by Lean. Those reviews remain source evidence; they do not override
the native log. The final review likewise does not certify the repaired
sources in the kernel.

## Root integration boundary

The actual direct package-path preflight exited **1**. It found missing or
untracked `HomotopyHypothesis` and `Atlas` package paths and an uninitialized
`GIFT` gitlink without its configuration. `InfoGeometryCore` was available.
This preflight is not a complete transitive dependency audit or a build.
No dependency pin, hook, or build helper was changed by this patch.

```bash
python3 tools/infra/ci_bootstrap.py paths --report /workspace/scratch/d8c17edeea4e/real-flow-path-preflight.json
```

The normal tracked pre-commit and pre-push hooks must be evaluated on the
candidate commit. Their actual commands, exits, and complete output belong to
the delivery record and PR description. A scoped native pass is not a substitute
for a failed root gate. Any publication exception must identify this candidate
and the observed outstanding gate; a prior PR's exception is not inherited.

## Exact source-analysis commands

These commands ran on the repaired hashes from the same repository root.
Their outputs and invocation records are preserved in
`evidence/source-analysis/` in the review bundle. The last scan's exit 1 is the
expected no-match result; all other commands exited 0.

### semantic-content

```bash
python3 tools/quality/semantic_content_audit.py --file-prefix lean/InfoGeometry/OperatorAlgebra/ExponentialGradeBounds.lean --file-prefix lean/InfoGeometry/OperatorAlgebra/QuadraticExponentialBounds.lean --file-prefix lean/InfoGeometry/OperatorAlgebra/TripotentExponentialBounds.lean --file-prefix lean/InfoGeometry/OperatorAlgebra/LoxodromicExponentialBounds.lean --gate --json-out /workspace/scratch/d8c17edeea4e/real-flow-qa-semantic-content.json --md-out /workspace/scratch/d8c17edeea4e/real-flow-qa-semantic-content.md
```

### staged-proof-proxy

```bash
python3 tools/quality/proof_proxy_staged_gate.py lean/InfoGeometry/OperatorAlgebra/ExponentialGradeBounds.lean lean/InfoGeometry/OperatorAlgebra/QuadraticExponentialBounds.lean lean/InfoGeometry/OperatorAlgebra/TripotentExponentialBounds.lean lean/InfoGeometry/OperatorAlgebra/LoxodromicExponentialBounds.lean
```

### placeholder-LoxodromicExponentialBounds

```bash
python3 tools/quality/placeholder_audit.py --root lean/InfoGeometry/OperatorAlgebra/LoxodromicExponentialBounds.lean --strict --format json --json-out /workspace/scratch/d8c17edeea4e/real-flow-qa-placeholder-LoxodromicExponentialBounds.json
```

### placeholder-TripotentExponentialBounds

```bash
python3 tools/quality/placeholder_audit.py --root lean/InfoGeometry/OperatorAlgebra/TripotentExponentialBounds.lean --strict --format json --json-out /workspace/scratch/d8c17edeea4e/real-flow-qa-placeholder-TripotentExponentialBounds.json
```

### placeholder-QuadraticExponentialBounds

```bash
python3 tools/quality/placeholder_audit.py --root lean/InfoGeometry/OperatorAlgebra/QuadraticExponentialBounds.lean --strict --format json --json-out /workspace/scratch/d8c17edeea4e/real-flow-qa-placeholder-QuadraticExponentialBounds.json
```

### placeholder-ExponentialGradeBounds

```bash
python3 tools/quality/placeholder_audit.py --root lean/InfoGeometry/OperatorAlgebra/ExponentialGradeBounds.lean --strict --format json --json-out /workspace/scratch/d8c17edeea4e/real-flow-qa-placeholder-ExponentialGradeBounds.json
```

### semantic-vacuity

```bash
python3 tools/quality/semantic_vacuity_gate.py lean/InfoGeometry/OperatorAlgebra/ExponentialGradeBounds.lean lean/InfoGeometry/OperatorAlgebra/QuadraticExponentialBounds.lean lean/InfoGeometry/OperatorAlgebra/TripotentExponentialBounds.lean lean/InfoGeometry/OperatorAlgebra/LoxodromicExponentialBounds.lean --fail-on error --json-out /workspace/scratch/d8c17edeea4e/real-flow-qa-semantic-vacuity.json
```

### strict-refute

```bash
python3 tools/infra/opengauss_cli.py refute lean/InfoGeometry/OperatorAlgebra/ExponentialGradeBounds.lean lean/InfoGeometry/OperatorAlgebra/QuadraticExponentialBounds.lean lean/InfoGeometry/OperatorAlgebra/TripotentExponentialBounds.lean lean/InfoGeometry/OperatorAlgebra/LoxodromicExponentialBounds.lean --strict --json
```

### gate4-source-review

```bash
python3 tools/infra/opengauss_cli.py review lean/InfoGeometry/OperatorAlgebra/ExponentialGradeBounds.lean lean/InfoGeometry/OperatorAlgebra/QuadraticExponentialBounds.lean lean/InfoGeometry/OperatorAlgebra/TripotentExponentialBounds.lean lean/InfoGeometry/OperatorAlgebra/LoxodromicExponentialBounds.lean --gate GATE_4 --json
```

### debt-source-scan

```bash
rg -n '\b(sorry|admit|axiom|native_decide|unsafe|partial|TODO|FIXME|stub|placeholder)\b' lean/InfoGeometry/OperatorAlgebra/ExponentialGradeBounds.lean lean/InfoGeometry/OperatorAlgebra/QuadraticExponentialBounds.lean lean/InfoGeometry/OperatorAlgebra/TripotentExponentialBounds.lean lean/InfoGeometry/OperatorAlgebra/LoxodromicExponentialBounds.lean
```
