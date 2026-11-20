# Alpöge announcement: source audit and finite Mangoldt smoothing

## Scope and provenance

This record concerns Levent Alpöge's four-page [announcement](https://alpo.ge/remark.pdf),
read on 2026-11-20, and the repository at upstream revision
`586c14bc9fb94eb09b56f7dc850d9d5297269f91`.

The downloaded announcement has SHA-256
`3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d`.
It is an announcement and a mathematical outline; it is not a self-contained
written proof. The paper links fourteen parts of an external Lean archive.
No part of that proof is imported by this change.

The source audit inspected the public
[mirror](https://github.com/CocoSgt/riemann-hypothesis-lean), including
[Main.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Main.lean),
[Statements.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Statements.lean),
and the final theorem entry points. The source-level RH target is Mathlib's
`RiemannHypothesis`, rather than a locally weakened replacement. The other
targets concern nonvanishing and critical-strip zeros of Dirichlet L-functions.
This inspected scope does not cover arbitrary automorphic L-functions or all
number-field zeta functions.

The [independent verification repository](https://github.com/Deicyde/riemann-hypothesis)
was inspected at revision `a172c464fd4bcfc4f53e394dcba45d742b1409a6`.
Its [README at that revision](https://github.com/Deicyde/riemann-hypothesis/blob/a172c464fd4bcfc4f53e394dcba45d742b1409a6/README.md)
reports that the full Comparator run on the submission has not yet run.
Its [successful CI run](https://github.com/Deicyde/riemann-hypothesis/actions/runs/44772223184)
checks original-archive identity and the independent statement file.
The [workflow](https://github.com/Deicyde/riemann-hypothesis/blob/a172c464fd4bcfc4f53e394dcba45d742b1409a6/.github/workflows/checks.yml)
does not compile the submitted proof. The challenge's intentional proof holes
specify comparison targets; they are neither defects found in the submitted
proof nor evidence that those targets have been proved.

This record establishes no verdict for the external RH/GRH proof. Complete
compilation, theorem-type comparison, axiom inspection, and independent proof
replay remain distinct checks. The external project uses Lean 4.33.1 and
Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; this repository retains
Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Repository findings

These are observations about inspected owner statements, not a new compilation
certificate for all the named files. The search covered related declarations,
definitions, imports, and consumers in `lean/` and `src/`, with bounded external
reference searches. No current declaration-graph certificate was available.

| Existing owner | Actual reusable content | Missing implication |
| --- | --- | --- |
| `Arithmetic/PrimeDistributionLaw.lean` | Native real von Mangoldt weights, finite Chebyshev sums and elementary positivity | Its asymptotic law predicates are not proofs of those laws |
| `Arithmetic/ActualRiemannZetaVonMangoldtBridge.lean` | Mathlib-backed identity between the von Mangoldt L-series and the negative logarithmic derivative of zeta on `1 < s.re` | Continuation to a prime/zero explicit formula and zero-location control |
| `Arithmetic/FiniteMangoldtDirichletConvolutionBridge.lean` | Native Möbius/Mangoldt divisor identities and finite operator evaluations | Global analytic estimates |
| `Algebra/FiniteGroupFourier.lean` and `LLM/WalshCharacterGeometry.lean` | Finite representation transforms and real binary-cube character orthogonality | Arithmetic theta lifts and their multiplicity estimates |
| `Arithmetic/FiniteWeilMangoldtQuadraticFormBridge.lean` | A finite form is Hermitian for a supplied self-adjoint operator family | Self-adjointness does not provide positivity or identify the arithmetic Weil distribution |
| `Canonical/HestenesKreinWeilCriterionColimit.lean` | Conditional transport of positivity through supplied readouts | `rh_of_colimitReadout` takes an arbitrary `RH : Prop`, a Weil-criterion equivalence, and the required readout identifications as hypotheses |
| `Automorphic/SiegelWeilKudlaRallisBridge.lean` | Consequences of explicit integral/formula witness fields | The theta-integral and Siegel-Weil equations themselves are supplied fields |
| `Arithmetic/RiemannHypothesisProjectiveFormulation.lean` | Equivalence of critical-line and Cayley-circle formulations for actual zeta zeros | Neither equivalent RH proposition is proved by this equivalence |

Some historical prose exceeds the owner statements. In particular,
`Canonical/GuinandWeilExplicitFormulaBridge.lean` proves norm-square positivity,
a coordinate fact about a point already placed on the critical line, and
prime-damping inequalities. It does not construct a spectral explicit formula.
`Arithmetic/ExplicitFormula.lean` receives its explicit formula as the
`hformula` argument. `Canonical/ExplicitFormulaZeroCounting.lean` defines its
counting expression from the displayed main term, and its `ZetaZero` structure
does not require `riemannZeta s = 0`. These surfaces cannot supply the missing
arithmetic proof merely by virtue of their names.

The existing `ExplicitFormula.smoothedChebyshevPsi` averages the two sides of
an integer jump. It is different from the weighted sum introduced below:
at `N = 2`, that average is `log 2 / 2`, whereas the new `S(2)` is zero.

## Exact theorem contract

Item 5 on PDF page 3 contains a positive-part smoothed von Mangoldt sum. The
new owner formalizes its integer-cutoff arithmetic component:

\[
A(N)=\sum_{n=0}^{N}\frac{\Lambda(n)}n,\qquad
S(N)=\sum_{n=0}^{N}\Lambda(n)\left(\frac Nn-1\right),\qquad N\in\mathbb N.
\]

All sums and values here lie in `ℝ`. The definitions reuse
`PrimeDistributionLaw.vonMangoldtWeight` and `chebyshevPsiFinite`; they do not
replace the von Mangoldt function by an abstract positive sequence. The zero
index contributes zero because the native function has `Λ(0) = 0`. The
positive-part identity explicitly separates this index before dividing.

The owner is `lean/InfoGeometry/Arithmetic/FiniteSmoothedMangoldt.lean`, extending
the existing namespace `InfoGeometry.Arithmetic.PrimeDistributionLaw`.

| Declaration | Exact statement or role |
| --- | --- |
| `harmonicMangoldtSum` | Defines `A(N)` |
| `smoothedMangoldtSum` | Defines `S(N)` |
| `smoothedMangoldtSum_eq_positivePart` | Agrees with `∑ Λ(n) max (N/n - 1) 0` at the integer cutoff |
| `smoothedMangoldtSum_eq_harmonic_sub_psi` | `S(N) = N A(N) - ψ(N)` |
| `smoothedMangoldtSum_succ_sub` | `S(N+1) - S(N) = A(N)` |
| `smoothedMangoldtSum_second_difference` | `S(N+2) - 2 S(N+1) + S(N) = Λ(N+1)/(N+1)` |
| `smoothedMangoldtSum_second_difference_nonneg` | Nonnegative discrete second difference |
| `smoothedMangoldtSum_second_difference_pos_iff` | Strict positivity exactly when `IsPrimePow (N+1)` |
| `vonMangoldtWeight_eq_mul_second_difference` | Recovers `Λ(N+1)` by multiplying the second difference by `N+1` |
| The two `*_monotone` theorems | Both `A` and `S` are monotone |

The first identity follows by distributing the finite sum. For the first
difference, the new endpoint has factor `(N+1)/(N+1)-1=0`, and each earlier
summand gains `Λ(n)/n`. Subtracting two first differences leaves precisely the
new term in `A`. Native Mathlib's `vonMangoldt_pos_iff` identifies its support.
This supplies actual dependency implications, without an analytic limit.

At the boundary, `S(0)=S(1)=S(2)=0`. The second difference at `N=0` is zero;
at `N=1` it is `log 2 / 2 > 0`. The audit companion exercises both cases.

## Scope barrier

The announcement also centers its statistic by terms involving
`-X log X + (1 + γ)X`. The nonnegativity proved here concerns the uncentered
finite sum `S`, and does not imply nonnegativity or any prescribed sign for the
centered expression. No centering estimate is assumed or proved.

This change does not construct a real-cutoff analytic extension, a Weil
distribution, a theta lift, an Iwasawa tower, a divisibility estimate, a
zero-counting measure, or RH/GRH. The new statements are entirely real; inherited
imports include the pre-existing finite-spin owner, which contains complex
matrix declarations. No claim is made that the full import closure is real-only.

## Verification and integration

The focused package at `verification/mangoldt-smoothing/` reads the actual
repository sources through `srcDir = "../../lean"`. Its nine dependency pins
match the root manifest. Its wrapper uses the repository's shared build lock
and rejects linked worktrees or symlinked Lake roots.

From the repository root, with the pinned Lean toolchain on `PATH`:

```bash
python3 verification/mangoldt-smoothing/check.py exe cache get Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
python3 verification/mangoldt-smoothing/check.py build InfoGeometry.Arithmetic.FiniteSmoothedMangoldtAudit
python3 verification/mangoldt-smoothing/check.py env lean lean/InfoGeometry/Arithmetic/FiniteSmoothedMangoldtAudit.lean
```

The companion audit lists both definitions and all sixteen theorems. Axiom
inspection must allow only `propext`, `Classical.choice`, and `Quot.sound`.
The owner is exposed through `InfoGeometry.Arithmetic.All`.

The independent semantic reviewer accepted the finite theorem contract and
its boundary cases. Independent QA reran the focused build with `--wfail`, a
fresh owner elaboration, and the audit command: all passed, with zero compiler
warnings. All eighteen public declarations reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. The independently generated
[validation record](../verification/mangoldt-smoothing/validation.json) preserves
commands, exit codes, source fingerprints, and warning classifications.
Its disposition is `ACCEPTED_WITH_LIMITED_SCOPE`. A focused build does not
certify the repository's full default targets or the external announced proof.

The semantic-vacuity gate with `--fail-on warning` returned exit code 1 for
two `trivial_surface` warnings, on the two cutoff-zero lemmas. The independent
semantic reviewer classified both as valid boundary evaluations of nonconstant
functions. The legacy vacuity linter also flagged the `omega` index-normalization
step and a syntactically unused cutoff parameter; these are reviewed heuristic
findings, not missing hypotheses. The positive prime example demonstrates
nonconstant behavior. The warnings are retained in the validation record;
theorems and gate settings were not changed to conceal them.

The root integration command was also attempted:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.All
```

It exited with code 1 during package resolution because
`external_refs/homotopy-hypothesis-lean4`, the configured `HomotopyHypothesis`
path dependency, is absent. Thus no root integration certificate is claimed.
The initial completion was kept local because the repository's `AGENTS.md`
and `.githooks/pre-push` require the root-package gate for publication. After
this blocker was reported, the user explicitly requested an upstream pull
request. Publication proceeds on that instruction with the root-build failure
disclosed for review. The focused acceptance remains limited to the finite
arithmetic development. Root policy, toolchain, and dependency pins are unchanged.
