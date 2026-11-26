# Semantic contract gap audit — 26 November 2026

## Scope and evidence

Reviewed baseline: [`fe24e350b08fdea04f74c0748ef9fd9417c47529`][baseline]. The source pins are Lean
`v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. This addendum records mathematical
deductions from exact owner definitions, counterexamples, conditional interfaces, and proposed
repairs. It complements the broader [historical gap-closure roadmap in PR #466][roadmap].

The diagnostic candidate is
[`GapRegression.lean`](../verification/contract-gap-regressions/GapRegression.lean). Its [validation
record](../verification/contract-gap-regressions/README.md) owns the compilation, axiom-audit, and
publication-gate results. This prose is source analysis; it does not independently certify any Lean
declaration.

Search coverage is bounded to the cited owners, their inspected imports and consumers, relevant
comparison owners, and the recent PRs listed below. An absent comparison in that search is recorded
as an open target, not a claim that no equivalent declaration exists anywhere in the repository.

## Priority and acceptance criteria

| Priority | Exact gap | Minimum closure criterion |
|---|---|---|
| P0 | Structural KMS seed has no nonzero witness | Construct a state on a represented noncommutative observable algebra and discharge its modular hypotheses |
| P0 | Uniform approximate-KMS bound is already exact | Bound the residual on unit balls or by the product of observable norms |
| P0 | Modular sign, core-trace scaling, and weight contracts | Reconcile conventions and instantiate genuine positive weight/core data |
| P0 | Combined build and publication evidence | Restore intended pinned dependencies and retain actual gate results |
| P1 | Phase-aligned Sinkhorn inequality does not prove convergence | Establish support hypotheses, a suitable descent estimate, and a `Tendsto` theorem |
| P1 | Legacy scalar ladder is empty | Migrate consumers to the existing noncommutative ladder owners |
| P1–P2 | Comparison and analytic endpoints | Prove the explicit maps and their metric, domain, differential, or topological compatibility |

These are engineering priorities. They are not a certified declaration DAG.

## 1. The all-operator KMS seed is empty

**Classification:** mathematical obstruction from owner definitions; the candidate's kernel status
is recorded separately.

[`SinkhornKMSCore.AlgebraEnd`][kms-core] is the full real bounded operator algebra on `DoubledSpace
F`. [`KMSSinkhornSeedState`][kms-seed] defines

\[
\operatorname{CommutatorOrthogonalOnOmega}(\Omega)
\iff \forall A,B,\quad \langle(AB-BA)\Omega,\Omega\rangle=0.
\]

`ExpectationSeedStructuralWitness` requires this condition and `Ω ≠ 0`, in addition to a
joint-kernel condition. No observable-subalgebra restriction appears in these quantifiers.

The [doubled-space owner][doubled] supplies the positive Hilbert product inner product; its
indefinite Krein form is a separate object. Set \(u=\Omega\ne0\) and
\(v=\operatorname{clockAxis}(u)\). Existing [norm/skew phase identities][tomita] give \(\langle
u,v\rangle=0\) and \(\|v\|=\|u\|>0\). Define actual bounded real rank-one maps

\[
A(w)=\langle v,w\rangle u,\qquad B(w)=\langle u,w\rangle v.
\]

Then \(Au=0\), \(Bu=\|u\|^2v\), and

\[
\langle(AB-BA)u,u\rangle
=\|u\|^4\|v\|^2=\|u\|^6>0.
\]

Consequently the owner predicate holds exactly at `Ω = 0`; the structural witness is empty for every
admissible carrier, generator, and temperature. The argument needs neither finite dimension nor a
scalar complex unit. It retains both ordered products of noncommuting real operators.

This is an obstruction to inhabiting this witness. It does not assert that Lean is inconsistent,
invalidate a conditional implication from the witness, or refute KMS states on represented
observable subalgebras. Consumers such as [weighted transport][weighted] and the [AQFT
interface][aqft] must be reviewed for claims of a constructed nonzero state.

**Repair:** parameterize the represented observable star algebra, construct a positive normalized
state, and derive the intended modular relation. Keep cyclicity of a vector (density of the
represented orbit) distinct from traciality of a functional (`ω (A * B) = ω (B * A)`). Restricting
to self-adjoint operators alone does not give an algebra closed under products. The [thermal
owner][thermal] explicitly supplies an algebraic KMS-like identity; analytic continuation, domains,
and its connection to the intended real doubled time evolution remain separate obligations.

## 2. Approximate KMS requires norm control

**Classification:** mathematical consequence of the current definition.

[`SatisfiesApproxKMSLike`][kms-core] bounds `kmsResidual K ω β A B` by one finite real `ε` for every
`A` and `B`, without norm constraints. Linearity gives

\[
R(tA,B)=|t|R(A,B).
\]

If any residual were positive, scaling `A` would violate the proposed bound. Thus the predicate
implies exact vanishing; for `ε ≥ 0` it is equivalent to exact vanishing. `SinkhornKMSControl`
repeats the same unrestricted quantifier. This obstruction is independent of the zero post-step RN
barrier.

**Repair:** require `ε ≥ 0` and either bound unit-ball observables or prove
\(R(A,B)\le\varepsilon\|A\|\|B\|\). Construct the estimate from the actual state and balancing
dynamics before using it as a quantitative thermal bound.

## 3. Modular and continuous-core contracts

### 3.1 Logarithm orientation and the scalar limitation

[`YangMillsContinuum.ModularRadonNikodymData`][yang-mills] starts with one positive real `r` and
defines \(\Delta=rI\), \(K=-\log(r)I\). The [continuous-core adapter][core] assigns `deltaLog := K`
while asking for \(\exp K=\Delta\). On a nonzero carrier this forces \(r^{-1}=r\), hence \(r=1\).
The intended distinction is

\[
\delta=\log\Delta,\qquad H_{\mathrm{mod}}=-\delta,\qquad
\exp(-H_{\mathrm{mod}})=\Delta.
\]

Reuse the negative-log orientation already present in
[`SpatialDerivativeBogoliubovIntertwiner`][spatial]. Its realization and chain laws are supplied
hypotheses, so it does not independently construct general spatial derivatives. A genuine
realization must discharge those hypotheses. Also, conjugation generated by scalar `K` is trivial
because `K` is central; these scalar data do not establish the desired Type III behavior.

### 3.2 Canonical core trace scaling

[`RealContinuousCoreInterface`][core] requires invariance under the dual action.
[`CoreTraceDatum.traceScalingUnderDualFlow`][weights] repeats that invariance. For the usual
continuous core, the canonical semifinite trace instead obeys

\[
\tau\circ\theta_t=e^{-t}\tau
\]

in the standard parameter convention. Reversing the parameter reverses the exponent; it does not
give invariance. [Haagerup's construction][haagerup] and [Hiai, Theorem 10.15][hiai] supply the
intended comparison. The invariant dual weight and the scaling canonical trace are different
objects.

**Repair:** define the core algebra, embedding, positive domain, and dual action, then construct the
trace with its scaling law. A real doubled realization needs a comparison preserving those
structures. Use extended nonnegative values on positive elements, or real values on an explicit
finite trace domain; `Core → ℝ` on an arbitrary type is insufficient for the target.

### 3.3 Semifiniteness is currently vacuous

Both [weight/trace records][weights] require a set `S` of positive elements on which the functional
is finite, with no approximation or cofinality condition. The empty set always supplies this field.
The weight record also lacks the required additivity and positive homogeneity laws.

**Repair:** use the actual positive order and the appropriate finite-domain approximation/supremum
characterization. Add the weight laws. State normality for the intended increasing nets, or justify
a sequential specialization. Acceptance requires a nontrivial instantiated model and compatibility
proofs.

## 4. The Sinkhorn inequality is not a convergence theorem

[`SinkhornFoundation`][sinkhorn] defines, for a row step, `phaseLyapunovBefore` as the old column
residual and `phaseLyapunovAfter` as the new row residual. The latter is zero after row
normalization. Their inequality does not prove descent of one fixed objective or convergence of the
trajectory.

For the strictly positive matrix

\[
A=\begin{pmatrix}3/4&1/2\\1/4&1/2\end{pmatrix},\qquad
R(A)=\begin{pmatrix}3/5&2/5\\1/3&2/3\end{pmatrix},
\]

the column sums change from `(1, 1)` to `(14/15, 16/15)`. The owner's absolute column residual
therefore increases from `0` to `2/15`. The candidate uses the existing normalization and residual
definitions. This counterexample does not refute the existing phase-aligned inequality or classical
Sinkhorn convergence.

**Repair:** distinguish support, total support, and full indecomposability; prove the hypotheses
needed by the selected conclusion. The original [Sinkhorn–Knopp theorem][sinkhorn-knopp]
distinguishes convergence, existence of positive diagonal scaling, and uniqueness of scaling
factors. Prove a suitable fixed-objective or two-step estimate, then a `Filter.Tendsto` result and
an error bound for consumers. The repaired normalized KMS estimate is a separate bridge requiring
its own proof.

## 5. Legacy scalar ladder has no witness

[`Peirce.PeirceLadderOperators`][scalar-ladder] stores real scalars `u` and `d` with `u * u = 0`, `d
* d = 0`, and `u * d + d * u = 1`. Over `ℝ`, the first equality forces `u = 0`, contradicting the
last equality. The candidate records emptiness of this exact legacy type.

This conclusion does not apply to the separate Clifford/operator ladder owners. Migrate the legacy
consumers to those noncommutative carriers and retain their actual CAR and adjoint hypotheses.

## 6. Geometric compatibility still needs a construction

The [conformal anomaly owner][conformal] assumes equality between the chiral scale and the RN
Kähler potential, together with unit relative volume, before deriving zero chiral scale. The
conditional implication is useful. The remaining synthesis is to derive that compatibility from
common noncommutative geometric data, or prove the appropriate bound if equality is too strong.
Packaging the equality as a witness does not construct it.

## 7. Comparison work after the contract repairs

The historical roadmap already covers these programs. The most useful next targets are explicit
comparison theorems, with the scope of each PR retained:

| Existing contribution | Next target |
|---|---|
| [Real uncertainty transport, #461][pr461] | Instantiate the actual wavelet transform, measure, admissibility, analytic domain, and intertwining hypotheses |
| [Phase-observable core, #462][pr462] and [finite Fock adjoints, #463][pr463] | Identify the quadratic Fock action with the existing exterior lift; prove bracket and metric/phase compatibility |
| [Bessel-Hagen/Maxwell, #464][pr464] | Differentiate the Maxwell Lagrangian and identify the corrected current with the stress current modulo the specified superpotential |
| [Graded Clifford symbol, #465][pr465] | Construct the continuous bundle symbol, relative class, and ABS comparison |

These proposed targets do not supply missing proofs merely by sharing names or physical
interpretations. The repair sequence is: construct nontrivial models; prove maps and preservation
laws; establish the required analytic or differential conclusions; derive the downstream
interpretation.

## Validation boundary

This document records source-backed analysis and mathematical arguments. The companion validation
record must name the exact candidate digest, commands, revisions, compiler results, axiom scope, and
remaining failures. A text scan, scoped compilation, semantic review, and complete repository build
are different checks. No whole-repository correctness claim follows from publishing this audit or
its diagnostic candidate.

[baseline]: https://github.com/nickgou-nuke/info-geometry-lean/tree/fe24e350b08fdea04f74c0748ef9fd9417c47529
[roadmap]: https://github.com/nickgou-nuke/info-geometry-lean/pull/466
[kms-core]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/Canonical/SinkhornKMSCore.lean
[kms-seed]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/Canonical/KMSSinkhornSeedState.lean
[doubled]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/Krein/DoubledSpace.lean
[tomita]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/Canonical/TomitaTakesaki.lean
[weighted]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/Canonical/KMSSinkhornWeightedTransport.lean
[aqft]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean
[thermal]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/Krein/Thermal.lean
[yang-mills]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/Canonical/YangMillsContinuum.lean
[core]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/Canonical/TypeIIIContinuousCoreReal.lean
[spatial]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/OperatorAlgebra/SpatialDerivativeBogoliubovIntertwiner.lean
[weights]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/OperatorAlgebra/ModularWeightTrace.lean
[sinkhorn]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/Canonical/SinkhornFoundation.lean
[scalar-ladder]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/Peirce/PeirceLadderOperators.lean
[conformal]: https://github.com/nickgou-nuke/info-geometry-lean/blob/fe24e350b08fdea04f74c0748ef9fd9417c47529/lean/InfoGeometry/Canonical/ConformalAnomalySource.lean
[haagerup]: https://www.isibang.ac.in/~soumyashant/misc/collected-works-of-haagerup/1970s/1979_Lp_spaces_associated_with_an_arbitrary_von_Neumann_algebra.pdf
[hiai]: https://arxiv.org/pdf/2004.02383
[sinkhorn-knopp]: https://msp.org/pjm/1967/21-2/pjm-v21-n2-p14-s.pdf
[pr461]: https://github.com/nickgou-nuke/info-geometry-lean/pull/461
[pr462]: https://github.com/nickgou-nuke/info-geometry-lean/pull/462
[pr463]: https://github.com/nickgou-nuke/info-geometry-lean/pull/463
[pr464]: https://github.com/nickgou-nuke/info-geometry-lean/pull/464
[pr465]: https://github.com/nickgou-nuke/info-geometry-lean/pull/465
