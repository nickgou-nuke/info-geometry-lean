# Dikin ellipsoids, Weyl scaling, and the arithmetic bound

## Result

Four native Lean owners extend PR #424. They prove real matrix scaling and
norm restoration, constructive positive-ray normalization, actual Mertens
bounds and a prescribed-scale boundedness equivalence, and the loss of
uniformity in Euler-mode barrier scaling. The complete contract is
[DIKIN_WEYL_BOUND_CONTRACT.md](DIKIN_WEYL_BOUND_CONTRACT.md).

The construction removes a supplied geometric smallness condition by choosing
an explicit scale. It does not remove the arithmetic uniformity requirement:
the scale reappears when the original norm or summatory function is recovered.
The near-square-root boundedness criterion is proved equivalent to the
existing cancellation premise, not asserted to be a consequence of arbitrary
normalization.

## 1. Full real matrix scaling

The owner [RealMatrixDikinScaling.lean](../lean/InfoGeometry/Analysis/RealMatrixDikinScaling.lean)
uses the existing real trace form with the actual matrix inverse:

\[
Q_A(H)=\operatorname{tr}((A^{-1}H)^2).
\]

For invertible real `A`, arbitrary real matrices `H,K`, and `c ≠ 0`, it proves

\[
Q_{cA}(H)=c^{-2}Q_A(H),\qquad
Q_A(cH)=c^2Q_A(H),\qquad
Q_{cA}(cH)=Q_A(H).
\]

The bilinear ordered inverse/trace form has the corresponding base-scaling
law. None of these results assumes `A*H = H*A`.

For `A.PosDef` and `H.IsSymm`, the owner constructs

\[
B=\sqrt{A^{-1}}\,H\sqrt{A^{-1}}
\]

using Mathlib's real matrix continuous functional calculus. It proves `B` is
symmetric and identifies the quadratic with its trace square and Frobenius
norm:

\[
Q_A(H)=\operatorname{tr}(B^2),\qquad
\sqrt{Q_A(H)}=\|B\|_{\mathrm F}.
\]

The existing cyclic trace theorem consumes this constructed square root.
There is no supplied diagonalization, inverse-square-root certificate, or
commuting surrogate.

Undoing the congruence gives the quantitative recovery theorem

\[
\|H\|_{\mathrm F}\le\operatorname{tr}(A)\sqrt{Q_A(H)}.
\]

For a positive Weyl scale `c` and `sqrt(Q_(cA)(H)) ≤ R`, this becomes

\[
\boxed{\|H\|_{\mathrm F}\le c\,\operatorname{tr}(A)R.}
\]

The trace is the ordinary, unnormalized trace. At `A = I_d` it equals `d`,
so the theorem does not hide a dimension factor.

Finally, the explicit scale

\[
c=1+\sqrt{Q_A(H)}
\]

is positive and yields `0 ≤ Q_(cA)(H) < 1`. This discharges a local quadratic
smallness condition. Recovering an ordinary bound still uses the displayed
scale and trace factors.

**Derivative scope.** The real theorem concerns the actual-inverse trace
quadratic owned by `SelfConcordant.hessianQuad`. It does not add a separate
native Fréchet derivative identification for a real-matrix potential. The
existing complex owner `Canonical/OperatorLogDetDikinGeometry.lean` already
has that stronger derivative identification on its own carrier.

## 2. Positive-ray normalization and its counterexample

[DikinWeylBoundedness.lean](../lean/InfoGeometry/Analysis/DikinWeylBoundedness.lean)
reuses `BurgStein.fisherScaleMetric x v = (v/x)^2` and
`AnalyticExcision.InDikin`. It proves, for `x > 0` and `R ≥ 0`,

\[
\operatorname{fisherScaleMetric}(x,v)\le R^2
\iff |v|\le Rx.
\]

The shifted Dikin predicate `InDikin x (x+v) R` is equivalent to this
quadratic bound. Common nonzero scaling of `x` and `v` preserves the metric.
For a family with positive bases, boundedness of the range of quadratics is
equivalent to a single radius constant, independent of the family index,
in the restored absolute estimate.

Every real value has the explicit adaptive normalization

\[
\sigma(v)=1+2|v|,\qquad
\operatorname{fisherScaleMetric}(\sigma(v),v)<\frac14.
\]

Thus every real sequence has bounded normalized quadratics at those adaptive
bases. A concrete Lean counterexample takes `v(N)=N`: the normalized
quadratics are bounded, while the range of the original sequence is not.
Existence of an unconstrained normalizing scale therefore cannot establish
an original absolute or arithmetic growth bound.

## 3. The actual Mertens sum

[MertensDikinBounds.lean](../lean/InfoGeometry/Arithmetic/MertensDikinBounds.lean)
uses the existing `mertensFunction` and native Möbius coefficients. Induction
from `M(0)=0`, the summatory recurrence, and `abs_moebius_le_one` proves

\[
|M(N)|\le N.
\]

The vanishing zero coefficient is retained. The result is the strict bound

\[
\operatorname{fisherScaleMetric}(N+1,M(N))<1.
\]

Every power scale `(N+1)^r` with `r ≥ 1` also has an unconditional quadratic
bound by one. These theorems require no RH or cancellation hypothesis.

The smaller prescribed scales give an exact equivalence:

\[
\begin{aligned}
&\texttt{MertensSquareRootCancellation}\\
&\quad\Longleftrightarrow
\forall\varepsilon>0,\quad
\operatorname{BddAbove}\left\{
\left(\frac{M(N)}{(N+1)^{1/2+\varepsilon}}\right)^2:N\in\mathbb N
\right\}.
\end{aligned}
\]

The forward implication uses the existing all-indices power bound. The
reverse implication extracts one radius constant for each epsilon and
restores the unshifted asymptotic estimate with

\[
(N+1)^r\le (2N)^r=2^rN^r\qquad(N\ge1).
\]

`riemannHypothesis_of_bddAbove_dikin` then invokes the already proved Mellin
route to Mathlib's `_root_.RiemannHypothesis`. Its uniform boundedness premise
remains unproved. The new equivalence makes that remaining premise explicit;
it does not rename it as a discharged assumption.

## 4. Euler-mode cutoff multiplier and obstruction

[ScaledEulerUniformBound.lean](../lean/InfoGeometry/Arithmetic/ScaledEulerUniformBound.lean)
reuses the exact existing `ScaledEulerNN` criterion. For positive energy, a
positive multiplier `c > 0`, and `0 < q < 1`, its NN slot inequality is equivalent to

\[
(1+q)^2\le4cq.
\]

The new constructive cutoff theorem chooses

\[
c(q_0)=\frac{(1+q_0)^2}{4q_0}
\]

and proves the inequality for all `q₀ ≤ q < 1`, where `0 < q₀ < 1`.
For any proposed bound `B`, the explicit point

\[
q=\frac1{8(|B|+1)}
\]

satisfies `0 < q < 1` and `B < (1+q)^2/(4q)`. Therefore no fixed positive
multiplier works throughout `(0,1)`, even for one fixed positive energy.

These statements concern the existing explicit derivative slots. The cutoff
multiplier is constant on its chosen interval. A point-dependent multiplier
of slots is not identified with derivatives of a variable-scaled potential;
such derivatives would include product-rule terms.

## 5. Deeper source search and remaining implications

This bounded audit inspected canonical and alternate `src/` definitions,
imports, hypotheses, and consumers, with native Mathlib source checks. A local
generated declaration-DAG index was unavailable; no complete graph search or
repository-wide absence claim is made.

| Source family | Source-confirmed content | Remaining input |
|---|---|---|
| `ProjectiveWeylGauge`, `WeylHomogeneousReadoutBridge` | Finite normalization identities and consequences of supplied homogeneity/factorization laws | No actual Mertens estimate follows from those fields |
| `BilingualAnalyticity` | Dikin/logarithmic-Hessian/Weyl neighborhood equivalence and common scaling | Uniform control at growing arithmetic cutoffs |
| `OperatorLogDetDikinGeometry` | Actual complex-matrix Fréchet Hessian, self-concordance, order bounds and cone containment | A quantitative arithmetic realization and limiting control |
| `HestenesKreinSelfConcordantBarrierColimit` | Hessian and Dikin transport under supplied compatibility, plus readout positivity transport | Constructed coercivity, compatibility, and uniform arithmetic bounds |
| Arithmetic `SelfConcordantZetaBarrier` | Formal C3 slots and model fields | Native derivative and zeta identifications are not supplied by the slots |
| Canonical IS barrier and `ISBarrierDerivativeBridge` | Actual scalar derivatives, positivity and unique minimum of finite prime barrier | The zero-to-minimum condition remains supplied |
| `MertensPartialTrace`, `PrimeMertensDefectBoundary` | A genuine Möbius sum in the former; model-bound implications in the latter | No inspected declaration derives actual near-square-root cancellation from scaling |

The canonical finite prime barrier's zero-to-minimum assumption already
implies critical-line zero location using its one-prime test. Scaling that
barrier by a positive constant preserves its minimizers and does not prove
that arithmetic zeros are minimizers. Introductory reflection claims for the
IS kernel are not supported by its proof bodies; the kernel
`x - log x - 1` is not invariant under `x ↦ 1/x`.

The alternate source
`src/InfoGeometry/Canonical/IntensiveLogDetPositivityTension.lean` contains a
dimension-normalization counterexample: at dimension `d+1`, the intensive
quadratic at `I` in direction `-2E₀₀` is `4/(d+1)`, although the perturbed
matrix is not positive semidefinite. That source was inspected, not compiled
as part of this extension. It is not included in the canonical validation.

Likewise, normalizing a vector in the existing real domain residual theorem
scales both sides of `|a|‖v‖ ≤ ‖Kv-bJv-av‖`. It neither constructs a nonzero
arithmetic mode nor changes the relative residual. The operator/domain
realization and the centered Mangoldt infinite analytic passage remain open.

## 6. Validation scope

The expanded audit lists 133 public declarations in 14 selected owners,
including the four new owners' 38 declarations. The initial PR validation
record is preserved unchanged. The extension's final checks and independent
review are recorded in
[`validation-dikin-weyl.json`](../verification/riemann-routes/validation-dikin-weyl.json).

The focused workflow repeats the selected-owner build, fresh elaboration
with warnings as errors, inventory/pin checks, and exact axiom parsing.
Existing dependency warnings and root integration limitations are reported
separately. No unconditional RH or whole-repository certificate is claimed.
