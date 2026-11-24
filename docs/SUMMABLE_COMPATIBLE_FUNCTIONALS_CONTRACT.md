# Summable defects and compatible real functionals

## Intake and owner

The 2026-11-24 RG attachment proposes a weighted Gaussian adapter and an
approximately compatible state construction. Its unchanged text is preserved
in [`intake-20261124.txt`](../verification/summable-compatible-functionals/intake-20261124.txt).
The raw intake SHA256 is:

```text
9bc02582c6f750ed96e115afc764ecbf9bab2c80bd9f6f3ca6feb1571e6ffb55
```

The new owner is
[`InfoGeometry.Canonical.SummableCompatibleFunctionals`](../lean/InfoGeometry/Canonical/SummableCompatibleFunctionals.lean).
It supplies the missing analytic implication from summable compatibility
defects to exactly compatible real readouts, then retains native positive
linear structure under additional hypotheses. Existing Gaussian owners and
adapter branches cover the other valid claims; the correction/reuse ledger
below records their scope.

Source review uses repository base
`fe24e350b08fdea04f74c0748ef9fd9417c47529`, Lean `v4.34.1`, and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The verification receipt, rather
than this base revision, identifies the exact source bytes compiled in a run.

## Exact scalar contract

For every stage $n\in\mathbb N$, let $A_n$ be a
`SeminormedAddCommGroup`. Let $\iota_n:A_n\to A_{n+1}$ and
$\omega_n:A_n\to\mathbb R$ be arbitrary functions. The hypotheses are:

| Hypothesis | Exact content |
| --- | --- |
| Nonnegative error | $0\le\varepsilon_n$ for every $n$ |
| Summability | `Summable ε` over the natural numbers |
| Norm bound on transitions | $\lVert\iota_n(a)\rVert\le\lVert a\rVert$ for every stage and input |
| Approximate compatibility | $\lvert\omega_{n+1}(\iota_n(a))-\omega_n(a)\rvert\le\varepsilon_n\lVert a\rVert$ |

The norm bound is the exact assumption: arbitrary transitions in this section
are not assumed additive, continuous, or Lipschitz with respect to distances.
The stage spaces need not be complete. Completeness is used for the real
codomain.

`refinedReadout` defines a finite pullback recursively:

$$
r_{n,a}(0)=\omega_n(a),\qquad
r_{n,a}(m+1)=r_{n+1,\iota_n(a)}(m).
$$

`abs_refinedReadout_succ_sub_le` transports the one-step bound to

$$
|r_{n,a}(m+1)-r_{n,a}(m)|\le\varepsilon_{n+m}\|a\|.
$$

The declaration `exists_compatible_limit_of_summable` concludes that there
exists a family $\omega^\infty_n:A_n\to\mathbb R$ satisfying all three
properties:

1. $r_{n,a}(m)\to\omega^\infty_n(a)$ as $m\to\infty$ for every fixed stage
   and input.
2. $\omega^\infty_{n+1}(\iota_n(a))=\omega^\infty_n(a)$.
3. The explicit remaining-tail estimate
   $$
   |\omega^\infty_n(a)-\omega_n(a)|
   \le\left(\sum_{k=0}^{\infty}\varepsilon_{n+k}\right)\|a\|.
   $$

This is pointwise convergence. The conclusion does not supply continuity,
linearity, or normalization for arbitrary original functions.

## Native positive linear construction

`exists_normalized_positive_compatible_limit` adds a `PartialOrder`,
`Module ℝ`, and distinguished element `1` (`One`) to each seminormed stage.
Transitions and original readouts are Mathlib's native positive linear maps:

```lean
ι : ∀ n, A n →ₚ[ℝ] A (n + 1)
ω : ∀ n, A n →ₚ[ℝ] ℝ
```

They satisfy the same norm and summable-defect hypotheses, together with
$\iota_n(1)=1$ and $\omega_n(1)=1$. No multiplication on the stages is
assumed; preservation of the distinguished `1` is the precise condition.

`refinedPositiveReadout` retains positivity and linearity through native
composition. Its evaluation agrees with `refinedReadout`, and
`refinedPositiveReadout_one` preserves normalization at every finite horizon.
The limiting construction uses `linearMapOfTendsto` to derive linearity,
closed-order limits in $\mathbb R$ to derive monotonicity, and the constant
limit at `1` to derive normalization. These properties are derived from the
finite maps, not assumed for the desired limit.

The resulting $\omega^\infty_n:A_n\to_p[\mathbb R]\mathbb R$ has the same
pointwise convergence and tail bound, and additionally satisfies:

```lean
(ω∞ (n + 1)).comp (ι n) = ω∞ n
refinedPositiveReadout ι ω∞ n m = ω∞ n
ω∞ n 1 = 1
```

The second identity holds for every stage and finite horizon. It concerns
pullbacks of the corrected limiting family; the original family is allowed
to have nonzero defects.

The dependency order is finite pullback → propagated defect → real Cauchy
limit → exact successor compatibility and tail bound → native positive linear
limit → every finite compatible pullback. The source imports only the needed
Mathlib normed-group, positive-linear-map, infinite-sum, and topological-module
owners. It reuses `cauchySeq_of_dist_le_of_summable`,
`dist_le_tsum_of_dist_le_of_tendsto₀`, `tendsto_add_atTop_iff_nat`,
`linearMapOfTendsto`, and native positive-map composition.

## Correction and reuse ledger

External references below are pinned to `MathePhysics/4D_Wilson_Loop_RG`
commit `9a4492cc6bdf3338379123a085af59dfd8018a9c`:
[EffectiveForm.lean][external-effective] and
[Convolution.lean][external-convolution].

| Intake claim | Corrected scope and disposition |
| --- | --- |
| Weighted Hessian with $Q^\dagger=wQ^T$, $B=Q^\dagger Q$, $R_{\rm lat}=(\alpha w)R$ | The valid identity is $A+Q^TR_{\rm lat}Q=A+\alpha(Q^\dagger RQ)$. At $R=I$, this is **$A+\alpha B$**, not $A+(\alpha w)B$. |
| External effective-form adjoint is already lattice weighted | `effStiffness α H Q` is `H + α • (LinearMap.adjoint Q ∘ₗ Q)` in ordinary Euclidean inner products. The file separately documents the lattice convention $Q_k^*=L^{kd}Q^T$. For fine/coarse scalar metric weights $f,c$, the adjoint is $(c/f)Q^T$. |
| External convolution needs a new general-$s$ theorem | `integral_blockKernel_mul_blockKernel` already assumes $s\ge0$ and $QQ^*=sI$, with $\gamma=\alpha\beta/(\beta+s\alpha)$. Its header identifies $s=L^{-d}$ for ordinary Euclidean block averages. |
| Proposed noncommuting witness certifies positivity and inverse-sensitive order | Its statement contains symmetry and noncommutation inequalities, but neither `PosDef` conclusions nor an inequality involving $R_1^{-1}$. Reuse the stronger positive noncommuting examples in PR452. |
| Scalar compatible limits are C-star states | Arbitrary scalar readouts yield only scalar limits. The new positive-linear theorem supplies explicit real linearity, positivity, and normalization hypotheses and conclusions; complex C-star state transport remains a separate owner boundary. |

The Hessian error has a one-dimensional positive counterexample: take
$A=Q=R=I$, $\alpha=1$, and $w=2$. Then $B=2I$ and
$R_{\rm lat}=2I$. The left side is $3I$, while the submitted specialization
$A+(\alpha w)B$ is $5I$.

The existing ordered operators are
$F=A+Q^HRQ$, $C=R^{-1}+QA^{-1}Q^H$,
$P=R-RQF^{-1}Q^HR$, and $H_{\rm ext}=F^{-1}Q^HR$.
Their multiplication order is retained; no commuting or diagonal surrogate
is introduced.

| Reviewed owner or work | Relevant declarations / reuse |
| --- | --- |
| Base [`PositiveCoarseGraining`](../lean/InfoGeometry/OperatorAlgebra/PositiveCoarseGraining.lean) | Positive fine/coarse precision and covariance, inverse identities, and harmonic-extension normal equations |
| Base [`CoarseGrainingVariational`](../lean/InfoGeometry/OperatorAlgebra/CoarseGrainingVariational.lean) and [`CoarseGrainingComposition`](../lean/InfoGeometry/OperatorAlgebra/CoarseGrainingComposition.lean) | Ordered quadratic completion, unique minimizers, and `twoStage_coarsePrecision_inv` |
| [PR452](https://github.com/nickgou-nuke/info-geometry-lean/pull/452), reviewed head `fffadd1048d757b0c3ad9f35c33ce009c6f321e6` | `GaussianNoiseComposition.coarsePrecision_scalar_noise`, `coarsePrecision_comp_scalar_noise`, native matrix Gaussian kernels/composition, and positive noncommuting examples |
| `codex/wilson-upstream-contributions-20261124`, reviewed head `4e9dd38fb2fb1032a115d8030d96a5e01398aef4` | [WeightedEffectiveForm.lean][weighted-effective]: `finePrecision_scalar_toEuclideanLin`, `harmonicExtension_scalar_eq`, `coarsePrecision_scalar_inner`, and `integral_blockKernel_mul_gaussian_coarsePrecision` |
| `codex/wilson-gaussian-upstream-20261124`, reviewed head `1c766dfd7980ffaa7723ff90a07c42797ffbf63c` | [MatrixWeighted][matrix-weighted] coordinate normal equations, Euclidean quadratic completion, and general matrix-weighted Gaussian integration |

These branch references record inspected existing work; they do not imply
that the branches are merged or imported by this addition. The new owner
adds no duplicate scalar precision formula, Gaussian composition theorem, or
`BalabanRGAdapter`.

## Real and complex state boundary

The base
[`CStarAlgebraStateColimit`](../lean/InfoGeometry/Canonical/CStarAlgebraStateColimit.lean)
owns `CStarStateColimit.Native.State A`. Its carrier requires
`CStarAlgebra A`, `PartialOrder A`, and `StarOrderedRing A`; its functional is
`A →ₚ[ℂ] ℂ`, normalized at `1`. `CompatibleStateFamily` restricts these states
along actual `StarAlgHom`s.

This addition constructs real positive linear limits on the stated stages.
It does not construct a complex extension, a C-star completion, a categorical
colimit universal property, a GNS representation, or a KMS state. The scalar
contract alone cannot provide linearity: with $A_n=\mathbb R$,
$\iota_n=\mathrm{id}$, $\varepsilon_n=0$, and $\omega_n(x)=x^2$, all its
hypotheses hold but the limit is nonlinear. The native positive-linear
variant addresses this precise missing structure without changing carriers.

## Verification and observed status

The [focused verification README](../verification/summable-compatible-functionals/README.md)
documents `check.py --phase build`, `--phase audit`, and `--phase final`.
The runner fixes this owner, uses the maintained shared lock and exact pins,
checks the resolved Lean/Lake runtime identity, and records source hashes and
native declaration axiom evidence in an isolated project. Its result does
not certify the root package or publication gate.

At documentation preparation on 2026-11-24, independent mathematical/source
review and the strict staged proof gate passed. The native focused build,
fresh owner elaboration, and declaration axiom audit are pending. These are
separate validation surfaces; source review and static screening are not
compiler evidence. Record the final run identifier, source hashes, and actual
outcome before promoting a kernel-verification claim.

[external-effective]: https://github.com/MathePhysics/4D_Wilson_Loop_RG/blob/9a4492cc6bdf3338379123a085af59dfd8018a9c/LEAN/Libraries/GaussianBlockSpin/GaussianBlockSpin/EffectiveForm.lean
[external-convolution]: https://github.com/MathePhysics/4D_Wilson_Loop_RG/blob/9a4492cc6bdf3338379123a085af59dfd8018a9c/LEAN/Libraries/GaussianBlockSpin/GaussianBlockSpin/Convolution.lean
[weighted-effective]: https://github.com/nickgou-nuke/info-geometry-lean/blob/4e9dd38fb2fb1032a115d8030d96a5e01398aef4/contributions/wilson/gaussian/GaussianBlockSpin/WeightedEffectiveForm.lean
[matrix-weighted]: https://github.com/nickgou-nuke/info-geometry-lean/tree/1c766dfd7980ffaa7723ff90a07c42797ffbf63c/contributions/wilson-gaussian/overlay/GaussianBlockSpin/MatrixWeighted
