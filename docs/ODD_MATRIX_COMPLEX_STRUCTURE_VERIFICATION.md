# Odd matrix size and internal complex structures: verification

## Source and review scope

This change continues upstream draft PR [#417](https://github.com/nickgou-nuke/info-geometry-lean/pull/417)
at `c9834db462b3798afef70c577ab19545e7e84b53`. The implementation commit is
`a0ef52d2d30faf1f60d80e676e8c6ef6de211cab`.

The four new owners contain **38 named declarations: 34 theorems and four
definitions**. Independent mathematical review covers each declaration and the
material reused constructions. Native generated/private declaration coverage
is recorded separately by the kernel audit below.

| Owner | Named declarations | Mathematical content |
| --- | ---: | --- |
| [Algebra.MatrixSquareNegOne](../lean/InfoGeometry/Algebra/MatrixSquareNegOne.lean) | 18 | Arbitrary-ring diagonal and scalar amplification; units and conjugation; right phase versus left matrix action; commutative odd-size classification; characteristic two; explicit noncommuting shear/phase pairs, an injective root family, and a fixed-metric counterexample. |
| [LinearAlgebra.RealMatrixSquareNegOne](../lean/InfoGeometry/LinearAlgebra/RealMatrixSquareNegOne.lean) | 9 | Real finite-size existence iff even dimension; native nested-matrix flattening; exact outer-size-three criterion; actual two-dimensional product-algebra counterexample. |
| [Algebra.QuaternionMatrixSquareNegOne](../lean/InfoGeometry/Algebra/QuaternionMatrixSquareNegOne.lean) | 4 | Native mixed diagonal of quaternion axes, generic noncommuting scalar amplification, and two concrete noncommuting roots in the actual three-by-three quaternion ring. |
| [Quantum.OperatorRingSquareNegOne](../lean/InfoGeometry/Quantum/OperatorRingSquareNegOne.lean) | 7 | Actual bounded doubled-space clock axis, continuous-equivalence conjugation and matrix amplification, and the native even-Clifford phase coefficient example. |

The [theorem contract](ODD_MATRIX_COMPLEX_STRUCTURE_CONTRACT.md) preserves the
intake, source provenance, corrections, hypotheses, and remaining targets.
`All.lean` imports the three consumer modules; they reach the generic core
transitively. Registration is not a whole-`All.lean` build certificate.

## Exact statements and corrections

### Coefficient roots and odd outer size

`scalar_square_eq_neg_one` uses the actual native `Matrix.scalar` ring
homomorphism over any associative unital ring. Centrality of the coefficient
is unnecessary. `diagonal_square_eq_neg_one_iff` permits different diagonal
roots without a pairwise commutation assumption. A negative-square element is
an actual unit with inverse its negative, and unit conjugation preserves and
reflects the square law.

For a **commutative ring** and an odd finite index cardinality,
`exists_matrix_square_eq_neg_one_iff_of_odd` proves

\[
(\exists A\in M_n(R),\ A^2=-I)\iff(\exists j\in R,\ j^2=-1).
\]

The forward witness is the native determinant; the reverse witness is scalar
amplification. Characteristic zero alone is not an obstruction. The determinant
argument is not applied to noncommutative coefficient rings.

With the minimal equation `(2 : R) = 0`,
`square_eq_neg_one_iff_sub_one_square_eq_zero` proves
`x*x = -1 ↔ (x-1)*(x-1) = 0`. It includes the zero ring and asserts no
spectral or diagonalizability result.

### Real dimensions and matrix coefficients

The real classifier reuses the existing parity obstruction in
`FiniteRealAnticommutation` and transports the existing
`Realification.internalJ` through an actual finite-index equivalence. It proves
existence exactly in even real column dimension, including dimension zero.
`Matrix.compRingEquiv` then transports the equation in both directions to prove

\[
\exists A\in M_m(M_k(\mathbb R)),\ A^2=-I
\quad\Longleftrightarrow\quad \operatorname{Even}(mk).
\]

The outer-size-three specialization is exactly `Even k`. Here `mk` is the
column-space dimension, not the real algebra dimension `m^2 k^2`.

The actual product algebra `ℝ × ℝ` has native `Module.finrank` equal to two.
Projecting coefficients onto the first factor excludes both a coefficient
root and every odd-size matrix root. Thus even total algebra dimension does
not suffice for arbitrary real coefficient algebras.

### Noncommutativity, phase action, and the metric

`mulVec_commutes_right_phase` uses Mathlib's opposite-ring scalar action:
componentwise right multiplication by `j` commutes with every left matrix
multiplication on coefficient columns. `right_phase_square` proves that this
right action squares to negation when `j*j=-1`. This is distinct from left
multiplication by the scalar matrix `j I`, whose noncommutation is exhibited
using the existing native quaternion axes.

The shear family is actual invertible conjugation of the existing universal
phase:

\[
P_t=\begin{pmatrix}1&t\\0&1\end{pmatrix},\qquad
J_t=P_tJ_0P_t^{-1}
 =\begin{pmatrix}t&-(1+t^2)\\1&-t\end{pmatrix}.
\]

Its `(0,0)` entry recovers `t`, giving genuine injectivity. Infinitude is proved
under `Infinite R` in `M_3(M_2(R))` by outer scalar amplification. Those outer
matrices are not asserted to be outer-nondiagonal or to classify all conjugates.

The source constructs native noncommuting pairs in `M₂(R)` for nontrivial
`R`, in `M₂(ℝ)`, and in `M₃(Quaternion ℝ)`. At `t=1`, the real phase has `(JᵀJ)₀₀=2`, not one. The concrete
`shearPhase_one_not_orthogonal` theorem is also consumed by the theorem giving
two noncommuting real roots, one failing fixed-metric orthogonality.

### Bounded operators and the native Clifford example

`Krein.clockAxis` acts on the actual `WithLp 2 (E × E)` carrier by
`(x,y) ↦ (-y,x)`. Its source proves its square law and norm preservation.
The new owner adapts that existing operator to multiplication in the native
continuous endomorphism ring and amplifies it to outer size three.

For a supplied `e : H ≃L[ℝ] DoubledSpace E`, the transported operator is the
actual native conjugation `e⁻¹ J e`. Its square law and boundedness are
established; a general continuous equivalence need not preserve the fixed
Hilbert metric. The proof does not construct self-doubling for every
infinite-dimensional real Hilbert space.

The Clifford consumer uses `Cl55InternalComplex.phaseBivector55` and its proved
square law in the actual even Clifford algebra. It neither introduces an
external complex scalar nor claims a full Clifford thermodynamic representation.

## Independent source review

The A-A reviewer did not author implementation sources or run any compiler,
test, or gate. The A-A review returned PASS for all 38 named declarations and traced
the substantive imported constructions, including the actual doubled-space
swap/sign involutions and the native Clifford and quaternion axes.

The first installed pre-commit attempt returned exit 1 with two T16 findings.
Its raw result is preserved. The generic module lacked a concrete closed
noncommutation witness in the form recognized by the source policy. The
quaternion module already proved noncommutation, but the checker's bounded
statement-form and binder recognition rejected that generic statement.
Independent A-A classified the latter diagnosis as a semantic false positive.

The response added three substantive concrete witness theorems, retaining the
useful generic API. No gate, helper, dependency pin, or tactic-trust setting
was weakened. The installed pre-commit retry passed with
`proof_proxy_staged_gate: ok` and created the implementation commit above.

## Scope limits

The universal infinite-dimensional Hilbert self-doubling construction, full
finite-dimensional real-algebra ideal classification, full quaternion conjugacy
classification, and Dieudonne determinant theory remain separate targets.
The contract links primary mathematical literature for the surrounding
classification statements without treating it as proof input.

These ring and matrix identities do not establish a Type III limit, a complete
Clifford representation of the thermodynamic state algebra, or a physical heat
cycle. Any such extension requires its own actual carrier, maps, positivity or
metric assumptions, and compatibility proofs.

## Fresh independent native verification

The independent QA context started from the frozen, clean implementation commit
above and used the maintained checker without `--incremental` or `--skip-audit`:

```bash
/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3 \
  tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/0b027a897d29/lean_verification_runtime/mathlib4 \
  --lean /workspace/scratch/0b027a897d29/lean_verification_runtime/lean-4.34.1/bin/lean \
  --output /workspace/scratch/0b027a897d29/odd-complex-verification/qa-final/kernel \
  --target InfoGeometry.Algebra.MatrixSquareNegOne \
  --target InfoGeometry.LinearAlgebra.RealMatrixSquareNegOne \
  --target InfoGeometry.Algebra.QuaternionMatrixSquareNegOne \
  --target InfoGeometry.Quantum.OperatorRingSquareNegOne
```

It ran on 2026-11-20 from 13:42:12.878702 to 13:44:17.684734 UTC and returned
**exit 0**. All **27 repository modules** in the resolved source closure were
compiled freshly, with `reused: false`. All four selected owners produced
**zero compiler warnings**. The unchanged prerequisites produced 33 compiler
warnings, preserved in the raw logs; this is not a warning-free-closure claim.

| Selected owner | Native owned declarations audited |
| --- | ---: |
| `Algebra.MatrixSquareNegOne` | 23 |
| `LinearAlgebra.RealMatrixSquareNegOne` | 11 |
| `Algebra.QuaternionMatrixSquareNegOne` | 5 |
| `Quantum.OperatorRingSquareNegOne` | 18 |
| **Total** | **57** |

This native enumeration includes generated/private declarations and is distinct
from the 38 named source declarations. Recursive axiom dependencies were exactly
`propext`, `Classical.choice`, and `Quot.sound`; no extra axiom was accepted.

The runtime was Lean `4.34.1`, commit
`5045d0056413266e57c625dcd7c365b10e377c52`, with unchanged Mathlib pin
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Preflight reconciled source, index,
freeze, A-A, and compiler snapshots, and confirmed the maintained helper and
pin files were unchanged from the PR base. Missing native artifacts were
restored through a narrowly scoped pinned-cache request; no cache was deleted
and no dependency revision was changed.

## Maintained static checks and separate adjudication

All four exact owner files were selected explicitly. The tools and gate
settings were unchanged.

| Check | Observed raw outcome |
| --- | --- |
| Strict OpenGauss source screen | Exit 0; no traps |
| Strict OpenGauss refutation | Exit 0; four PASS reports |
| Gate 4 source preflight | Exit 0; four `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED` reports |
| Style `audit_file` API | Four files; zero findings |
| Lexical `scan_files` API | Four files; zero gaps or read failures |
| Strict placeholder audits | Four exits 0; zero hard/advisory findings; two SOFT `skeletal-proof` signals |
| Semantic vacuity at `--fail-on warning` | **Exit 1**; two `trivial_surface` warnings |
| Workflow syntax and registration | Passed: four Bash bodies, three embedded Python blocks, all 27 closure paths and nine additional required paths covered; three terminal imports reach all four owners |
| Source reconciliation | All 49 monitored paths matched source/index snapshots; compiler sources, freeze, and A-A hashes reconciled; implementation worktree remained clean |

Gate 4 is a source preflight; it is not represented as kernel verification.
The separately executed fresh native checker supplies that evidence. Likewise,
style and lexical scans do not substitute for mathematical review or the
recursive declaration axiom audit.

The independent A-A review examined every emitted finding rather than treating
short native proofs as automatically defective:

| Raw finding | Declaration and disposition |
| --- | --- |
| Semantic `trivial_surface` warning | `RealMatrixSquareNegOne.real_prod_finrank` computes the actual native product-module dimension using Mathlib's factor dimensions. The result is consumed by the even-dimensional coefficient-algebra counterexample. A short `simp` proof discharges the complete statement. Semantically nonblocking. |
| Semantic `trivial_surface` warning | `OperatorRingSquareNegOne.transportedClockAxis_apply` is the correctly scoped `[simp]` evaluation formula for the actual conjugation definition. It exposes the correct `e.symm (J (e x))` orientation; no direct named downstream consumer is claimed. It is an API readback, not an assumed square law or an analytic existence theorem. Semantically nonblocking. |
| Placeholder SOFT `skeletal-proof` signal | `MatrixSquareNegOne.scalar_square_eq_neg_one` is native ring-homomorphism transport of multiplication, negation, and one, with substantive matrix and operator consumers. Its short complete proof contains no placeholder. Semantically nonblocking. |
| Placeholder SOFT `skeletal-proof` signal | `RealMatrixSquareNegOne.real_prod_finrank` is the same actual dimension calculation reviewed above. Its native automated proof establishes the dimension needed by the counterexample. Semantically nonblocking. |

The semantic-vacuity **raw exit remains 1** and both SOFT labels remain in the
receipts. No heuristic was disabled, no proof was padded with artificial steps,
and no failed check is reported as an automatic pass. The separate A-A
adjudication requests no mathematical source correction.

The exact source commands were:

```text
python tools/infra/opengauss_screener.py <four-owner-paths> --strict --json
python tools/infra/opengauss_cli.py refute <four-owner-paths> --strict --json
python tools/infra/opengauss_cli.py review <four-owner-paths> --gate GATE_4 --json
python tools/quality/placeholder_audit.py --root <each-owner> --strict --json-out <report> --signals-out <signals>
python tools/quality/semantic_vacuity_gate.py <four-owner-paths> --fail-on warning --json-out <report>
git diff --cached --check
git diff --check
```

The style and lexical tools were invoked through their maintained `audit_file`
and `scan_files` APIs on each of the four exact files. Command arrays, times,
exit codes, source snapshots, and log hashes are retained in the QA receipts.

## Root integration and installed publication checks

The parent then ran the maintained root wrapper, separately from the accepted
native source closure:

```bash
python3 tools/infra/run_locked_lean.py \
  --lake /workspace/scratch/0b027a897d29/lean_verification_runtime/lean-4.34.1/bin/lake \
  lean/InfoGeometry/Quantum/OperatorRingSquareNegOne.lean
```

On 2026-11-20 it ran from 13:46:29.460906 to 13:47:00.877947 UTC and returned
**exit 1**, before compiling the selected owner:

```text
error: HomotopyHypothesis: package directory not found:
.../external_refs/homotopy-hypothesis-lean4
```

The root manifest records this as a local path dependency rather than a
reconstructible Git revision. No guessed revision, replacement package, proof
stub, changed dependency pin, or destructive cache repair was introduced.

The installed pre-commit retry passed and created the implementation commit.
The actual installed pre-push hook was then invoked with that exact checked-out
commit and a new remote branch:

```text
refs/heads/codex/odd-matrix-internal-complex-20261120 a0ef52d2d30faf1f60d80e676e8c6ef6de211cab refs/heads/codex/odd-matrix-internal-complex-20261120 0000000000000000000000000000000000000000
```

```bash
bash .githooks/pre-push origin https://github.com/nickgou-nuke/info-geometry-lean.git
```

It ran from 13:47:00.881951 to 13:50:46.757693 UTC and returned **exit 1**.
The hook classified the complete new-ref ancestry range from merge base
`08c34e03f610b452e03422037949196dc7d92d6d` against `origin/main`.
Its locked Lake build selected **28 changed owners**, including `All`, and
failed during package resolution at the same missing HomotopyHypothesis path.
The subsequent 28-file lexical axiom/debt audit, semantic-content audit,
tracked Lean scope audit, and quarantine audit passed their respective gates.
Historical quarantine findings remain visible and are not new proof results.

Because the ancestry-range gate failed, the hook did not reach its later full
root-package invocation. This is a **failed publication-gate result**, not a
successful whole-project build. The user requested upstream PR publication;
the accompanying draft presents the checked result for review with this
integration failure disclosed and no merge performed. This documentation-only
follow-up does not change the accepted proof, workflow, helper, or pin bytes.

## Scoped hosted workflow

[odd-matrix-complex.yml](../.github/workflows/odd-matrix-complex.yml) checks the
exact PR-head revision. It verifies the unchanged Lean/Mathlib pins and the Lean
archive checksum before execution, restores dependency artifacts only, computes
native import roots under the shared lock, and compiles fresh repository
artifacts for each attempt. It requires the exact four targets, zero warnings
on those targets, complete owned-declaration counts, and the native recursive
axiom audit. All 27 repository closure paths are covered by triggers; the
verification document itself is also a trigger.

Its uploaded artifact contains that hosted attempt's reports, logs, provenance,
and source snapshots. Workflow parsing and source review are not an observed
hosted run. The PR description records hosted execution separately with its
actual source head and run URL; it must not substitute a prior PR's CI result.

## Accepted source fingerprints

These SHA-256 values identify the independently reviewed and freshly compiled
source bytes. This later verification document is outside that frozen snapshot.

| Path | SHA-256 |
| --- | --- |
| `docs/ODD_MATRIX_COMPLEX_STRUCTURE_CONTRACT.md` | `bcca864225b300d306aee83305e7481efe80fef99786cf9b194f69b8877ed334` |
| `lean/InfoGeometry/Algebra/MatrixSquareNegOne.lean` | `a610e29a7d74f388f1a5c6d6d9e0f2bd5b9ddcdc92603799d611a27ae35e7668` |
| `lean/InfoGeometry/LinearAlgebra/RealMatrixSquareNegOne.lean` | `fcba25b1b922e238beff056c334abe8237b3e1a94a5aecdeff25b602463482e0` |
| `lean/InfoGeometry/Algebra/QuaternionMatrixSquareNegOne.lean` | `3d3c4b13ad4969c41145efe249fe1a45ee304595bbf45fe5d5c49f1f39e449a4` |
| `lean/InfoGeometry/Quantum/OperatorRingSquareNegOne.lean` | `b51dd2c358bc75edb0c025a020b61dc134b8be005dd7c7d5e0ebb0011029c170` |
| `lean/InfoGeometry/All.lean` | `d3adca9c6980f847228f10930f9e0a4b1071d1be653a792793ba179ae467cd4c` |
| `.github/workflows/odd-matrix-complex.yml` | `bd26e8c82657bbf4fd5bfbcddbee44d966d29f439848ad7eac64727c2c73b526` |

## Evidence fingerprints

The local receipts preserve exact commands, UTC timestamps, raw exits, source
snapshots, and log hashes. This document contains their substantive results and
all heuristic dispositions. The separate hosted workflow supplies reviewable
raw kernel evidence for its own exact remote source revision.

| Receipt or log | SHA-256 |
| --- | --- |
| `aa-source-review-v1.json` | `8f78a6ff0dd7d6325d9770d34c87b7960f8bbbe62fd4caa3a5caaa3b3bbf1ea7` |
| `aa-source-review.json` | `90ba9351687c8b3c2cc14724c1f250497a09118f3ef851c701ee5397b3853b18` |
| `aa-static-review.json` | `3f2e68b1791b1dbeecb62801a943371048f201e5c49bb33a62f45f4040d30c9d` |
| `source-freeze.json` | `c950a3e86bd3ed319f44869ff6c93af22632622fef236f5df0302cef0d1eefd9` |
| `qa-final/qa-report.json` | `e0020e3ca3fc030e10ab7b2365d25724a2cdb6e87eed62ffbc019515801ef758` |
| `qa-final/qa-report.md` | `be1547d944e46afe3c5fe2baeff4abc981d8b0996869869d6679a2a6994b76d6` |
| `qa-final/qa-evidence-sha256.json` | `4f2630f4ecc98fe14f9ae50a3b49075c22ae864935e84722db94b60ea8252b89` |
| `qa-final/kernel/report.json` | `d762fd1aa07659ebba1005ca84ccde070abd53903bdbd41420480e7d640166d6` |
| `qa-final/kernel/axioms.log` | `dcfc3e6bc7379a4752c42858cda5cbfa9670a3798c9ea373ad0b2beb1ec19db9` |
| `qa-final/static/semantic-vacuity.json` | `1c0bd5ded40da964c182a80b3414dd94296e83588ccddedf238621c1fea01475` |
| `qa-final/static-commands.json` | `fb48b8e013634169d77e61f2b52539bfef6112835dd96546be4417e6e5f5a3ef` |
| `implementation-commit.log` | `4acf0b9540c85d8f0928f3b9d58681355dc6c6af25ffd720b712e671705a2234` |
| `implementation-commit-final.log` | `58945e3030d2a2cf07710ac1055a2ebc074f909a5125a76834dcd642dd72720e` |
| `root-lake.log` | `6dc6b338679a6a7d0e6c1b5f3bbc6f1f0cf7f55d5f89a7c33b76de791d134f57` |
| `installed-pre-push.log` | `9c42d4de1ca503382b3e35203a92361c14bb18922023dc013a8c01d9b4c2034f` |
| `integration-commands.json` | `e507cb319f1d26c870658d910405e5f1538884547d4e6ce91993cf3ad61a70a8` |
