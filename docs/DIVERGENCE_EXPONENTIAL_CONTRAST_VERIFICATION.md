# Real coupled exponentials and finite KL contrast geometry

## Source and scope

**Result: `[accepted_limited_scope]`** for the native theorem surface described
below. Root Lake and publication-gate results are reported separately.

This follow-up implements the remaining finite analytic bridges in the
[corrected theorem contract](DIVERGENCE_EXPONENTIAL_CONTRAST_CONTRACT.md).
The implementation commit is `2d5ab998e21f6f6bb1950cdce1acedd803d80dec`, tree
`e3cbeb2955b7938740803e0399cc1ea7f2092d2e`. Its parent source tree is identical
to upstream PR [#419](https://github.com/nickgou-nuke/info-geometry-lean/pull/419),
head `8aa3a5ba924ac451e069e1a60c4e5dc0bcd02136`. The PR is a follow-up on that
branch; the existing internal-complex-structure work is retained.

The new proof owners are:

- [Analysis/EvenOddExponential.lean](../lean/InfoGeometry/Analysis/EvenOddExponential.lean)
- [NCG/GradedCoupledExponential.lean](../lean/InfoGeometry/NCG/GradedCoupledExponential.lean)
- [InformationGeometry/PositiveMeasureContrast.lean](../lean/InfoGeometry/InformationGeometry/PositiveMeasureContrast.lean)

They are registered in `InfoGeometry.All`. Registration is separate from
successful compilation of that full aggregate. The existing scoped divergence
workflow now selects its original nine owners plus these three, with all
51 repository source-closure paths included in its trigger list.

## Exact mathematical results

### 1. Norm-convergent real algebra kernels

For `[NormedRing A] [NormedAlgebra ℝ A]`, the definitions are

```text
F(Z) = Σ k≥0, ((2k)!)⁻¹ • Z^k
G(Z) = Σ k≥0, ((2k+1)!)⁻¹ • Z^k.
```

Both norm series are proved summable by comparison with Mathlib's exponential
series. With `[CompleteSpace A]`, the algebra-valued sums converge and

```text
exp H    = F(H²) + H * G(H²)
exp (-H) = F(H²) - H * G(H²).
```

`F(0) = G(0) = 1`. The proofs use the native exponential's `HasSum` and the
even/odd partition of its series. They do not stipulate an exponential or
assume the desired identity. The carrier need not be commutative; H need not
be invertible or diagonalizable. No matrix square root or inverse square
root is introduced. The owner proves everywhere absolute convergence and
the exponential identities; it does not package an additional analytic-map
or general functional-calculus interface.

Main declarations: `summable_norm_evenExpKernel`,
`summable_norm_oddExpKernel`, `summable_evenExpKernel`,
`summable_oddExpKernel`, `exp_eq_evenExpKernel_add_mul_oddExpKernel`, and
`exp_neg_eq_evenExpKernel_sub_mul_oddExpKernel`.

### 2. Coupled full real matrices and a proved pivot

For arbitrary finite real square blocks U,V and real scalar beta,

```text
H  = beta * Gamma + [[0,U],[V,0]],     Gamma = [[I,0],[0,-I]],
W+ = beta² I + UV,                    W- = beta² I + VU.
```

`coupledGenerator_sq` proves `H² = diag(W+,W-)` without `UV = VU`.
`exp_neg_coupledGenerator` proves the full matrix identity

```text
exp(-H) = [[F(W+) - beta G(W+),  -U G(W-)],
           [-V G(W+),             F(W-) + beta G(W-)]].
```

All multiplication orders are retained. For a general matrix-valued diagonal
coefficient B, `coupled_square_with_commutators` instead proves

```text
[[B,U],[V,-B]]² = [[B²+UV, BU-UB], [VB-BV, B²+VU]].
```

`coupled_square_blockDiagonal_iff` proves that the simpler block-diagonal
square holds exactly when B commutes with both U and V. The generic kernel
identity still applies to H when these commutators do not vanish.
`exp_neg_add_smul_one` separates the common real scalar identity channel
through actual centrality.

For a real symmetric H, `exp_neg_posDef` proves that its actual native
exponential is positive definite. `exp_neg_pivot_posDef` proves the same for
the lower-right principal block D. `exp_neg_pivot_twoSidedInverse` supplies
both equations for the native inverse, and `exp_neg_gaussian_factorization`
applies the existing ring-level UDL theorem to the actual exponential.
The pivot assumption is discharged in this symmetric class, not inferred
from mere invertibility of the full exponential.

Two concrete `2 × 2` block witnesses establish that this symmetric class
includes noncommuting U,V and that a noncentral B can leave a nonzero
off-diagonal square. The resulting generators act on a `4 × 4` real space;
the general theorems are not restricted to that witness dimension.

### 3. Actual second Fréchet derivative and the separate neutral form

The ambient function uses the existing finite generalized KL summands:

```text
D(p,q) = Σ i, p_i log(p_i/q_i) - p_i + q_i.
```

`jointGeneralizedKL_eq_generalizedKL` identifies it with the existing
positive-measure divergence. `firstVariation` and `jointHessian` are native
continuous linear maps. Crucially, `hasFDerivAt_fderiv_jointGeneralizedKL`
proves the derivative of the actual `fderiv ℝ jointGeneralizedKL`, using
an open positive neighborhood to identify its first derivative with the
explicit variation. This is stronger than stipulating a bilinear formula or
only differentiating along one affine curve.

At coincidence p=q=r, with every r_i positive,

```text
D²D[(u,v),(u',v')] = Σ i, (u_i-v_i)(u'_i-v'_i)/r_i,
-D²D[(u,0),(0,v)]  = g_r(u,v) = Σ i, u_i v_i/r_i.
```

The full joint Hessian is positive semidefinite, and its actual pairing
kernel is exactly `u=v`. The negative mixed block is the positive-definite
Fisher form. The owner separately constructs

```text
G_r((u,v),(u',v')) = g_r(u,v') + g_r(v,u'),
K(u,v)             = (u,-v).
```

`neutralForm_eq_negative_mixed_second_fderiv` explicitly connects this
form to the two mixed blocks of the native Hessian. `neutralForm_nondegenerate`
proves nondegeneracy, and `fisherParaComplex`, `fisherNeutralDatum`, and
`fisherNondegenerateDatum` instantiate the existing canonical structures.
Their involution, symmetry, anti-isometry, and cross-sheet nondegeneracy
fields are proved from the actual positive weights. The fundamental form is
the existing weighted split symplectic pairing. Explicit opposite-sign
directions distinguish this neutral form from the degenerate joint Hessian.

These are finite algebraic geometric data at each positive measure. No
manifold, connection, integrability, closed differential form, or global
para-Kähler structure is inferred. No normalization of the positive measure
is required.

## Existing bridges reused and checked

The attachment's relative modular logarithm/expectation bridge and general
dimensional SPD scale/shape bridge already have concrete owners. This change
does not introduce copies of them.

- `Canonical.MatrixRelativeModular` constructs the actual full matrix
  superoperator, its native CFC logarithm and positivity, and the generalized
  relative-entropy expectation including both mass corrections.
- `Canonical.MatrixRelativeModularPhysicsBridge` identifies the existing
  regular bimodule action and operator IS expression, then derives the Gibbs
  balance without supplying the invalid abstract modular chain law.
- `Jordan.BurgStein` and `Canonical.GaussianBurgStein` retain full covariance
  matrices, the exact scale-weighted shape term, and both nonnegativity
  results. `Y⁻¹X` and its determinant-one shape are not silently assumed
  symmetric; the Gaussian consumer uses the actual SPD covariance `s⁻¹X`.
- `InformationGeometry.PositiveMeasureDifferential` remains the owner of
  the existing first and affine second derivatives. The new contrast owner
  adds the genuine operator-valued Fréchet derivative and its consumers.

The retained nine targets also include product-measure KL, actual Gaussian
KL and its trace/logdet evaluation, and finite exponential-family analytic KL.

## Acceptance evidence

### Independent roles and source review

Generation, source audit, and acceptance were assigned to distinct roles.
The independent A-A reviewed all 68 named source declarations: 14 definitions
and 54 theorems, including 8 private declarations, plus the anonymous local
rational-norm instance. The verdict was **PASS for source audit** at the
implementation revision above, with no blocking mathematical finding.

The audit traced the genuine norm-series convergence, native exponential,
ordered block products, constructed positive pivot, actual second Fréchet
derivative, and concretely instantiated neutral structures. It checked the
noncommuting and noncentral-defect witnesses and corrected the contract's
annihilator wording: each isotropic eigenspace is its own annihilator;
opposite eigenspaces pair nondegenerately. It did not run a compiler, test,
screener, or native axiom check, and did not author these proofs.

The independent source-audit JSON has SHA256
`8f563af8e1fcc648c75eb35cd91672e2aad0cebe84e9a3b666ecac55fba95b4e`;
its readable report has SHA256
`a44bbcccee6650a1af17b254a32b6d04200a90e2bff321d936c0f98f0fc080fb`.

### Installed staged proof gate

The first actual pre-commit invocation returned **exit 1**. Its T16 source
scanner did not recognize scalar `ring` calculations nested in bilinear-map
constructors, or the explicit matrix witness stated using `¬ Commute U V`.
The final source uses ordinary distributivity/reassociation lemmas for those
linearity obligations and states the same witness as `U * V ≠ V * U`.
Both changed owners were recompiled successfully with zero warnings.

The second actual `git commit` invocation ran the unchanged installed hook,
reported `proof_proxy_staged_gate: ok`, and created the implementation commit.
No checker, severity setting, dependency pin, or proof-trust setting was
changed. The first failure is retained separately from the successful retry.

### Independent fresh native verification

The distinct QA agent ran the unchanged maintained source-closure checker
from 14:44:22.568453 to 14:47:49.260271 UTC on 2026-11-20. It returned
**exit 0** with:

- **51 repository modules freshly compiled**, with no reused repository
  artifacts and no incremental mode;
- **all twelve selected owners at zero warnings**;
- **305 owned compiled declarations audited**, including private and
  compiler-generated declarations;
- only `propext`, `Classical.choice`, and `Quot.sound` in the recursive axiom
  footprint;
- unchanged source, helper, dependency-pin, hook, workflow, and registration
  fingerprints at final reconciliation.

The three new owners contribute 132 native declarations: 17 in
`EvenOddExponential`, 33 in `GradedCoupledExponential`, and 82 in
`PositiveMeasureContrast`. The retained nine owners contribute 173.
These are compiled declaration counts, not counts of authored theorem
statements.

The exact checker invocation was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/0b027a897d29/lean_verification_runtime/mathlib4 \
  --lean /workspace/scratch/0b027a897d29/lean_verification_runtime/lean-4.34.1/bin/lean \
  --output /workspace/scratch/0b027a897d29/divergence-bridges-verification/qa-fresh \
  --target InfoGeometry.Jordan.BurgStein \
  --target InfoGeometry.Probability.KullbackLeiblerProduct \
  --target InfoGeometry.Probability.GaussianKullbackLeibler \
  --target InfoGeometry.Probability.GaussianTraceLogdet \
  --target InfoGeometry.InformationGeometry.PositiveMeasureDifferential \
  --target InfoGeometry.ExponentialFamily.FiniteAnalyticKL \
  --target InfoGeometry.Canonical.MatrixRelativeModular \
  --target InfoGeometry.Canonical.MatrixRelativeModularPhysicsBridge \
  --target InfoGeometry.Canonical.GaussianBurgStein \
  --target InfoGeometry.Analysis.EvenOddExponential \
  --target InfoGeometry.NCG.GradedCoupledExponential \
  --target InfoGeometry.InformationGeometry.PositiveMeasureContrast
```

The checker itself has a warning gate specialized to its original
Clifford-Dirac targets. QA therefore separately asserted zero warnings for
each of these twelve explicitly selected owners, as the expanded hosted
workflow also does. It also checked every closure module had `reused=false`,
the exact selected target order, all declaration counts, and the native
audit's success.

The closure includes **47 warnings in thirteen unchanged prerequisite
modules**. They are not attributed to the selected-owner zero-warning result:

| Unchanged prerequisite | Warnings |
| --- | ---: |
| `InformationGeometry.ItakuraSaitoBregmanBridge` | 1 |
| `ExponentialFamily.Finite` | 1 |
| `Canonical.MatrixDetExpTraceJacobi` | 5 |
| `Canonical.QuantumRelativeSurprisal` | 1 |
| `Canonical.ArakiItakuraSaitoEquivalence` | 1 |
| `Canonical.FiniteMatrixGibbsFunctional` | 4 |
| `Canonical.FreeEnergyDissipationRate` | 1 |
| `Canonical.FreeEnergyEquilibriumUnitaryBridge` | 1 |
| `Physics.RegularBimoduleCommutant` | 13 |
| `Physics.FiniteRelativeModularOperator` | 1 |
| `NCG.BerezinianGaussianFactorization` | 3 |
| `Probability.FiniteMarkovWeightedAdjoint` | 10 |
| `Canonical.ParaComplexConnectionBridge` | 5 |

The native checker report has SHA256
`c5da51301290bff91705ff688c25ec0eedcf3c03f7dbd8268cb69fd9e2b1fee0`.
The independent QA receipt has SHA256
`160eb74bf69cbe00bc18aca2e57814aabba2e6a6aab6bcab33353ba6fbc3e0bb`;
its evidence manifest has SHA256
`5d65b31fa44382285b7b7a8cbca6a731ca91e258a2abb7abaf53df8aecc7a7cf`.

### Separate source-only checks

QA ran the unchanged OpenGauss screen, refuter and Gate 4 source review,
strict placeholder audits, style and lexical scans, whitespace checks, and
workflow syntax/registration checks. These passed their respective enforced
conditions. Workflow verification covered the exact twelve targets, all
51 closure triggers, four Bash bodies, three Python bodies, and the three
terminal `All.lean` registrations; it did not compile the full aggregate.

The warning-strict semantic-vacuity command returned **exit 1**, with seven
`trivial_surface` warnings. Placeholder audits also retained five SOFT
skeletal-proof signals while passing their strict hard-stop conditions.
These raw results are preserved and are not described as a clean heuristic
report. The independent A-A dispositions are recorded below.

The independent A-A read every flagged declaration and required no source
change. Its disposition is source review, not a retroactive pass for the
warning-strict command:

| Flagged declaration | Source-grounded disposition |
| --- | --- |
| `sourceCoord_apply` | Private definitional readback of a native continuous coordinate projection. |
| `referenceCoord_apply` | Corresponding private projection readback for the reference coordinate. |
| `jointGeneralizedKL_eq_generalizedKL` | Exact identification with the existing finite sum; differentiability is proved separately. |
| `fisherForm_symm` | Complete termwise symmetry proof using real multiplication commutativity, with no operator-carrier change. |
| `neutralForm_apply` | Readback of the native bilinear form after its four linearity laws are proved; nondegeneracy and Hessian compatibility are separate theorems. |
| `gamma_anticommutes_offDiagonal` | Complete actual block calculation over arbitrary `Ring R`; opposite signs cancel without `UV=VU`. |
| `coupledGenerator_eq` | Exact representation identity from the grading, scalar action, and block addition; no exponential conclusion is assumed. |

The five SOFT placeholder signals repeat the latter five declarations.
Their generated recommendations remain preserved in the raw reports.
The disposition JSON has SHA256
`7ae6a2a0d0a80daeb424aa86becf68837a4ded9df953e6e246555ffc58d6534a`;
its readable report has SHA256
`53f0cc49b50f17a3f306450b6a7b7d7f9c34cea9cf4ea9fb240b6657b3cf6fb6`.

## Root integration and publication scope

The parent ran the maintained root file entry point separately:

```bash
python3 tools/infra/run_locked_lean.py \
  --lake /workspace/scratch/0b027a897d29/lean_verification_runtime/lean-4.34.1/bin/lake \
  lean/InfoGeometry/InformationGeometry/PositiveMeasureContrast.lean
```

It ran from 14:49:20.319420 to 14:49:22.528631 UTC on 2026-11-20 and
returned **exit 1**, before compiling the selected source:

```text
error: HomotopyHypothesis: package directory not found:
.../external_refs/homotopy-hypothesis-lean4
```

The root manifest identifies this as a local path dependency, without a
reconstructible Git revision. No guessed replacement revision, dependency
stub, pin change, or destructive cache repair was introduced.

The actual installed pre-push hook was then invoked against the exact
implementation commit as a new remote branch:

```text
refs/heads/codex/divergence-exponential-contrast-20261120 2d5ab998e21f6f6bb1950cdce1acedd803d80dec refs/heads/codex/divergence-exponential-contrast-20261120 0000000000000000000000000000000000000000
```

```bash
bash .githooks/pre-push origin https://github.com/nickgou-nuke/info-geometry-lean.git
```

It ran from 14:49:54.380806 to 14:53:25.456134 UTC and returned **exit 1**.
Its new-ref ancestry classification selected **31 changed owners**, including
the aggregate. The maintained locked Lake build stopped during package
resolution at the same missing HomotopyHypothesis path. The later lexical
axiom/debt audit, semantic-content audit, tracked Lean scope audit, and
quarantine audit passed their respective conditions. Existing quarantine
debt remains visible in those reports and is not presented as checked proof.

Because this ancestry-range gate failed, the hook did not reach its later
full root-package invocation. This is a **failed publication-gate result**;
neither the root package nor the full `All.lean` aggregate is accepted by
this record. The authorized upstream PR presents the separately checked
theorems for review with this integration failure disclosed. No merge is
performed.

The root file-check log has SHA256
`c4886c5b82090f4e42468899f532d73b1ea779406b4790cb030e1670f2bcbf85`;
the actual installed pre-push log has SHA256
`419ee4ab140ba08733528568025e5326a460f96665fb91d5cc40867db4ef21e3`.

The expanded hosted workflow fetches the exact PR-head source, verifies the
unchanged Lean archive checksum and Mathlib pin, restores dependency artifacts
only, recompiles all selected repository sources, and audits every owned
declaration. Hosted run URLs and outcomes are recorded in the PR description
after execution; this local record does not infer a hosted pass from local
verification.

## Source fingerprints

| File | SHA256 |
| --- | --- |
| `Analysis/EvenOddExponential.lean` | `6b0c455143da9053d2d32aef94588df1ba090da2ddae5201caa8b8137ad5049a` |
| `NCG/GradedCoupledExponential.lean` | `de38d4a6768d0f12e0a916ad509e27b42cf6e6653618f0fabca31594d84c4f9a` |
| `InformationGeometry/PositiveMeasureContrast.lean` | `6a3e07222ca39770bcb83f8e39fdd03f3e5724f119684ee8128cd915da3aba0e` |
| `.github/workflows/divergence-modular-closure.yml` | `2b509c2e3f5f132128f684d75ba454f118c99d113e21c15bf6ca3eb63dcc5b7d` |
| `docs/DIVERGENCE_EXPONENTIAL_CONTRAST_CONTRACT.md` | `4a001d00e7463f26bb62369db0b4b64d205db6a35691193fbf1e6b8b661f0913` |

The toolchain remains Lean `4.34.1`; Mathlib remains pinned at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The verification helpers, tracked
hooks, and dependency pins are unchanged. This verification-document follow-up
does not change the accepted owner or workflow bytes above.
