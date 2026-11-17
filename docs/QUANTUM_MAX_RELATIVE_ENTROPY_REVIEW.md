# Quantum max-relative entropy: source and verification record

## Source and selected claims

The [theorem contract](QUANTUM_MAX_RELATIVE_ENTROPY_CONTRACT.md) fixes the supplied
PDF hash, native carriers, dependency pins and scope. The implementation starts
from upstream main `08c34e03f610b452e03422037949196dc7d92d6d`; it does not depend on
the unmerged bimetric PR or any other draft branch.

The independent paper audit read pp. 6–58 and Appendix A, pp. 70–71 of
*Entropic measures of quantum information*, arXiv:2611.08254v1. It did not audit
the whole continuous-variable section. The implementation selects Eq. (150)
and the following measurement paragraph on p. 32, which was also checked in a
rendered page image. The broader audit supplied 65 claim records; that inventory
is navigation and mathematical review, not a claim of 65 formalized theorems.

| Source claim or recurring construction | Native realization in this change | Boundary |
|---|---|---|
| Operator domination, Eq. (150) | Strictly positive finite `NNReal` factors and native order | Matrix consumers use Loewner order, not entrywise order. |
| Extremization over admissible bounds | Complete-lattice infimum in `ENNReal` | No optimizer or inverse-support formula is asserted. |
| Extended divergence | `ENNReal.log : ENNReal → EReal` | Natural logarithm; zero factor gives negative infinity, infeasibility positive infinity. |
| Loss of distinguishability under a map | Proven factor and divergence DPI for native positive linear maps | Positivity and linearity suffice; this is not an assumed DPI field. |
| Concrete quantum processing | Existing square finite Kraus map, with native real scalar restriction | The concrete consumer has equal input/output dimension. |
| State normalization | Native positive trace functional; existing Kraus completeness theorem | Trace one gives a lower bound of one on the factor and zero on the divergence. |
| Observation by effects | Loewner order iff all PSD trace tests, iff all effects `0 ≤ E ≤ I` | Hermitian inputs; normalized native rank-one probes prove the converse. |
| Support obstruction | Positive trace witness and a kernel-vector criterion force infinity | The converse support-inclusion theorem remains open debt here. |
| Noncommuting boundary example | Existing Bloch matrices at `(0,0,1)`, `(1,0,0)` and `(-1,0,0)` | Exact `Fin 2` complex matrices; no classical diagonal replacement. |

## Existing owners and dependency order

The bounded repository survey inspected 31 relevant owner files and verified
their bytes against the base revision. The main reused owners are
`ChoiCompletePositivity`, `KrausBoundaryDuality`, `PositiveBoundaryConditioning`,
and `DensityMatrixPurity`. Their existing theorems provide the actual Kraus
operation, positivity, trace preservation and positive trace pairing.
`OperatorAlgebra.NoncommutativeRenyi` remains the owner of the CFC kernels.

The dependency sequence is concrete: native matrix positivity and trace laws
give positive trace tests; native rank-one probes give their converse and
effect normalization; feasible-factor transport gives infimum DPI; the
extended logarithm gives divergence DPI; the existing Kraus operation supplies
the channel consumer. A positive input weight with zero reference weight then
excludes every finite factor. No operational or asymptotic conclusion is
inserted as an extra dependency.

The explicit qubit pair has

\[
\rho=\begin{pmatrix}1&0\\0&0\end{pmatrix},\quad
\sigma=\tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix},\quad
E=\tfrac12\begin{pmatrix}1&-1\\-1&1\end{pmatrix}.
\]

The new source proves positivity and trace one, `ρ * σ ≠ σ * ρ`, `0 ≤ E ≤ I`,
`Tr(ρE)=1/2` and `Tr(σE)=0`, and connects these identities to the actual
extended divergence's infinite value. Native acceptance is reported separately
below; mathematical source review alone is not compilation.

## Independent review and correction

Generation, source/mathematical audit (A-A), and acceptance QA are different
agent roles. Both independent reviewers found the same documentation issue:
`D < +∞` is not two-sided finiteness on general inputs, since `D = −∞` is
possible. The generic theorem docstring and contract now state exclusion of
positive infinity. The separately proved normalized-input lower bound prevents
negative infinity on states. The theorem type and positive-factor convention
were unchanged by this correction.

The reviewers inspected the pinned Mathlib declarations for native Loewner and
complex order, PSD rank-one probes, normalized star projections, positive trace
maps, extended-log monotonicity and the quadratic-form kernel criterion.
They also checked that the Kraus consumer uses the actual existing matrix map.
Final dispositions and exact source hashes belong to the acceptance receipts
and PR body. Initial source review is not a native verification certificate.

The first two installed pre-commit runs rejected the qubit file under its T16
noncommutativity detector. Its bounded syntax recognizer did not identify the
existing `densityMatrix` function applications as typed witness constants,
either in `¬Commute` or explicit product-inequality form. The source states
`ρ * σ ≠ σ * ρ` with the same entrywise witness and now directly imports the
existing `FiniteSpinAlgebra` owner, whose closed complex-matrix witness
`j_plus_j_minus_ne` meets that gate's explicit-import contract. This module was
already a transitive dependency. No new algebra, duplicate witness definitions,
or gate changes were introduced. Actual retry outcomes are recorded separately.

## Verification status at the source checkpoint

The toolchain is unchanged: Lean `leanprover/lean4:v4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The preliminary local generic-owner checker reached the maintained shared-lock
wait. It has no observed native result at this checkpoint. Its copied source
predates the documentation correction, so that preliminary snapshot cannot
certify the final source hashes. A final all-owner run is required.

Native elaboration, zero selected-owner warnings, the declaration-axiom audit,
and the root-package/push gate remain separate required checks. Static scans,
source review and a draft PR do not establish any of those results. The PR body
and workflow artifacts record subsequent outcomes with exact revisions.

## Focused native workflow

`.github/workflows/quantum-max-relative-entropy.yml` invokes the unchanged
maintained `tools/quality/check_clifford_dirac.py` with these exact targets:

```text
InfoGeometry.OperatorAlgebra.MaxRelativeEntropy
InfoGeometry.Quantum.PositiveEffectOrder
InfoGeometry.Quantum.MaxRelativeEntropy
InfoGeometry.Quantum.MaxRelativeEntropyQubit
```

It checks out the exact PR head, verifies both pins, restores only dependency
artifacts, hydrates the observed Mathlib import roots under the shared lock,
and compiles fresh repository artifacts. It uses neither `--incremental` nor
`--skip-audit`. It additionally rejects compiler warnings in each selected
owner; the checker's historical warning-prefix filter does not by itself
cover the new namespaces.

The native audit must examine every declaration owned by the four selected
modules, allowing only `propext`, `Classical.choice` and `Quot.sound`. Source
and verification-helper hashes, warning counts, native declaration counts,
and complete audit output are preserved in the attempt artifact. Executed
workflow revision and checked source revision are recorded separately.

This source-closure check does not certify the root Lake package or the
`InfoGeometry.All` umbrella. Their integration and push gates are tracked
separately. Pending or queued native checks remain pending.

## Remaining mathematical scope

This change does not establish tensor additivity, the inverse-on-support norm
formula, the converse support criterion, measured/prepared optimization over
all channels, Umegaki DPI, Rényi parameter ranges, recovery, smoothing,
regularization, or asymptotic/continuous-variable results. In particular,
equalities of extended divergences at infinity are not promoted into finite
equality-characterization or recovery theorems.
