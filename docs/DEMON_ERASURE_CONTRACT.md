# Finite-bath erasure, projective coarse graining, and finite fluctuation bounds

## Status and provenance

The Lean proofs in this change have been independently reviewed at the source
and pinned-API level. Native compilation and declaration-axiom acceptance are
separate gates; see [the verification record](DEMON_ERASURE_VERIFICATION.md).
Statements below describe the actual proposed Lean types, not an acceptance
certificate for the attachment's physical synthesis.

The user's attachment is preserved byte for byte in
[DEMON_ERASURE_INTAKE.md](DEMON_ERASURE_INTAKE.md):

- Original supplied name: `Pasted text(20261117-134447).txt`.
- Size: **39,770 bytes**.
- SHA256: `8c5c0a9caccde73f643e18476a1baa182fa1957b50a57a6b6143d17bc8455c49`.
- Source base: `08c34e03f610b452e03422037949196dc7d92d6d`.
- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The dependency pins are unchanged. The original intake remains a research
input, including its incorrect or unsupported statements; this contract is
the corrected interpretation. No psychological or hidden-reasoning extraction
is claimed.

## 1. Exact carriers and useful constructions

| Owner | Actual carrier and operations | Derived content |
|---|---|---|
| `Quantum.MatrixTensorRank` | Linear maps over a field, native tensor products and ranges; full finite square matrices and `Matrix.kronecker` | Tensor-map range dimensions and matrix tensor ranks multiply. |
| `Quantum.FiniteBathErasure` | Full complex matrices, native matrix positivity, star projections, unitary conjugation, actual finite partial trace, existing CFC Gibbs matrices | A projection marginal forces both support identities; the resulting rank bound obstructs a pure marginal for a mixed system with a faithful finite bath. |
| `Quantum.PureAuxiliarySwap` | Native permutation matrix and unitary group on two equal finite factors, arbitrary full input matrices, actual partial trace | SWAP exchanges the tensor factors; a supplied normalized pure auxiliary gives exact erasure, explicitly outside the faithful-bath hypothesis. |
| `Quantum.ProjectiveCoarseGraining` | A complex-linear map on all `Matrix (Fin d) (Fin d) ℂ`, arbitrary finite macro index and arbitrary finite ancillary index | Positive and completely positive block-uniform replacement; trace, identity, macro readouts, idempotence, fixed matrices, and density preservation under the stated projector hypotheses. |
| `Probability.FiniteFluctuationBound` | Existing finite positive normalized forward/backward probability functions; actual real logarithm and finite expectation | Nonnegative expected production, its exact equality case, the expected work/correction ledger, corrected work bound, and zero-correction specializations. |

The probability results are finite classical probability statements in their
own right. They do not replace the noncommuting matrix operations in the
quantum constructions.

### 1.1 Tensor rank and support

The tensor-rank proof uses the existing range identity for `TensorProduct.map`,
the injective tensor inclusion of subspaces over a field, and native dimension
formulas. The unrestricted linear-map lemma does not introduce an unnecessary
finite-dimensional assumption. The matrix specialization uses native tensor
bases and `Matrix.toLin_kronecker`:

\[
\operatorname{rank}(A\otimes B)
=\operatorname{rank}(A)\operatorname{rank}(B).
\]

For a positive full joint matrix \(\sigma\), an arbitrary star projection
\(P\), and its actual second-factor marginal, the key support theorem is

\[
\operatorname{Tr}_B\sigma=P
\quad\Longrightarrow\quad
(P\otimes I_B)\sigma=\sigma
\quad\text{and}\quad
\sigma(P\otimes I_B)=\sigma.
\]

The proof constructs a Gram factor from native positivity. Zero trace against
the complementary projection then annihilates that component. It does not
assume the desired support conclusion or a product decomposition. Taking
matrix ranks gives

\[
\operatorname{rank}\sigma\le\operatorname{rank}(P)\,d_B.
\]

The erasure theorem assumes:

1. A positive system matrix \(\rho\) with \(1<\operatorname{rank}\rho\).
2. A positive bath matrix \(\gamma\) that is a unit in the full matrix algebra.
3. A nonempty finite bath index and initial product \(\rho\otimes\gamma\).
4. An arbitrary unitary on the full product-index matrix space.
5. An arbitrary normalized target vector \(v\), with pure target
   \(P=vv^\dagger\).

Unitary rank invariance and tensor-rank multiplication give
\(\operatorname{rank}\sigma=\operatorname{rank}\rho\,d_B>d_B\).
The support bound for \(vv^\dagger\) gives the incompatible upper bound
\(\operatorname{rank}\sigma\le d_B\).
Initial trace-one hypotheses are unnecessary for this stronger algebraic
obstruction. For density matrices, the usual physical interpretation applies.

The Gibbs corollary uses the repository's actual normalized CFC Gibbs state.
Its invertibility is proved from the existing invertible Gibbs weight and
nonzero partition function. The real parameter is finite and need not be
positive for this algebraic result. There is no zero-temperature limit,
infinite-dimensional bath, resource-time estimate, or energy-conservation
assumption hidden in the theorem.

The companion `PureAuxiliarySwap` owner supplies the boundary construction:
the actual coordinate-SWAP permutation is a unitary, and for an arbitrary
trace-one system matrix and normalized vector \(v\),

\[
\operatorname{Tr}_B\bigl[U_{\rm swap}(\rho\otimes vv^\dagger)
U_{\rm swap}^\dagger\bigr]=vv^\dagger.
\]

The same existential theorem derives positivity, trace one, and projection
purity of the supplied auxiliary. It applies to positive density inputs;
input positivity is unnecessary for the stronger trace identity. The
auxiliary is not asserted to be a faithful Gibbs state. Its preparation cost
and availability are outside this finite algebraic construction.

### 1.2 Block-uniform coarse state

The constructed map is

\[
E_P(X)=\sum_i\frac{\operatorname{Tr}(P_iX)}{\operatorname{Tr}(P_i)}P_i.
\]

Every input matrix is allowed. In particular, there is no hypothesis
\([X,P_i]=0\). Zero projectors contribute zero; the native positive-matrix
trace-zero theorem justifies their treatment without a blanket nonzero-volume
assumption.

| Property | Required projector hypotheses |
|---|---|
| Complex linearity | None. |
| Positivity and complete positivity at every finite ancillary size | Each \(P_i\) is a star projection. |
| Trace preservation and unitality | Star projections and \(\sum_iP_i=I\). |
| Macro-readout preservation, idempotence, and the fixed-matrix characterization | Star projections and \(P_iP_j=0\) for \(i\ne j\). |
| Density preservation | Star projections, completeness, positive input, and input trace one. |

The fixed matrices are exactly the finite sums \(\sum_i c_iP_i\). The
amplification is proved equal to a sum of actual block compressions followed
by the existing replacement channels. Complete positivity is then derived
from native compression positivity and `replacement_completely_positive_all`.

This map differs from the existing Peirce pinching channel: pinching retains
the full matrix inside each block, whereas this map uniformly fills each
block while retaining its trace. No duplicate pinching API is introduced.

### 1.3 Finite fluctuation and work consequences

The existing carrier is
`InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus.DirectedThermoGraph.IntegralFluctuationLaw`.
Its fields are strictly positive, normalized forward and backward probability
functions \(p,q\) on the same finite sample space. Its definitions are

\[
\Sigma(\omega)=\log\frac{p(\omega)}{q(\omega)},
\qquad \mathbb E_p f=\sum_\omega p(\omega)f(\omega).
\]

The existing owner already proves \(\mathbb E_p e^{-\Sigma}=1\). The new
expectation results consume that theorem and the existing finite Jensen and
KL equality owners:

\[
\mathbb E_p\Sigma\ge0,
\qquad
\mathbb E_p\Sigma=0\iff p=q.
\]

The generic exponential-moment lemma permits zero weights, assuming
\(p\ge0\), \(\sum p=1\), and \(\sum p e^{-X}\le1\). The likelihood carrier's
strict positivity remains intact; this extension does not silently assert a
fluctuation identity for dynamics with missing support.

For \(\beta>0\), the physical interpretation requires the explicit pathwise
premise

\[
\Sigma(\omega)=\beta\bigl(W(\omega)-\Delta F(\omega)\bigr)+\delta(\omega).
\]

Finite-sum linearity proves the exact expectation ledger, and Jensen gives

\[
\mathbb E_pW-\mathbb E_p\Delta F
\ge-\frac{\mathbb E_p\delta}{\beta}.
\]

Saturation is equivalent to \(p=q\) under that same pathwise premise. Separate
theorems specialize to zero correction. Neither the premise nor the equality
criterion constructs reverse dynamics, a stopping time, or an attainable
physical protocol.

## 2. Established dependency order

The dependency order is the order of actual reused lemmas, not an inferred
physical causal relation between metaphors in the intake.

| Upstream construction | Established use | Downstream result |
|---|---|---|
| Tensor-map range and injective tensor inclusion | Native finrank transport to tensor bases | Full Kronecker-rank multiplication. |
| Native positive Gram factor and trace adjointness | Complementary trace zero implies complementary support zero | Both ordered support identities for a projection marginal. |
| Support identities, tensor rank, and unitary rank | Compare joint lower and upper rank bounds | Faithful finite-bath erasure obstruction. |
| Existing Gibbs-weight invertibility and nonzero partition | Invertibility survives actual normalization | Normalized-Gibbs erasure corollary. |
| Native permutation multiplication and established permutation unitarity | Actual SWAP conjugation exchanges the full tensor factors | Exact partial-trace erasure with a supplied pure auxiliary. |
| Actual `blockK` compression and replacement-channel amplification | Amplification equals a sum of positive terms | Complete positivity of the block-uniform map. |
| Existing likelihood IFT and finite negative-log Jensen | Exponential moment bounds its ordinary finite mean | Nonnegative mean production. |
| Existing finite KL zero characterization and explicit work identity | Equality and finite-sum linearity | Corrected work saturation iff the two probability functions agree. |

There is no formal edge asserting that the matrix rank theorem implies the
fluctuation law, an entropy-gradient flow, or a universal resource divergence.

## 3. Owner search and reuse record

Searches covered related names, definitions, hypotheses, imports, and consumers
under `lean`, `src`, and `proofs`, followed by inspection of the relevant owner
sources and pinned Mathlib APIs. These are bounded source searches, not a
claim that every tracked declaration has been inspected.

| Existing owner | Reused fact or exact boundary |
|---|---|
| `Quantum.FinitePartialTrace` | Actual product-index `partialTraceSecondOp`, total trace, and diagonal marginal. |
| `QuantumContext.MatrixStagePartialTrace` | Existing full-matrix trace-adjointness declaration; moved unchanged to the focused partial-trace owner, with its qualified name preserved. |
| `Canonical.FiniteMatrixGibbsFunctional` | Actual CFC Gibbs density, invertibility, and nonzero partition normalization. |
| `Quantum.MatrixBoundaryPurification` | Actual normalized Gibbs state, positivity and trace-one properties. |
| `Quantum.KrausAmplificationCP` | Actual finite block amplification and compression identities. |
| `Quantum.ChoiCompletePositivity` | Established permutation-matrix unitarity, used to construct the native SWAP unitary witness. |
| `Quantum.ReplacementStateChannel` | Full-matrix replacement channel and complete positivity for every finite ancillary type. |
| `OperatorAlgebra.PeirceSpine.PeircePinchingChannel` | Existing two-projector pinching, with its distinct internal-block behavior. |
| `Canonical.MatrixEntropyUnitaryOrbit` | Actual `CFC.log` entropy and unitary invariance under strict positivity; no singular-state or Klein-inequality conclusion is inferred. |
| `Canonical.QuantumRelativeSurprisal` | Trace algebra with supplied modular logarithms; it does not independently construct the required logarithms or prove their relative-entropy inequality. |
| `Inference.FiniteRelativeEntropyEquality` | Positive normalized finite KL equals zero exactly when its probability functions agree. |
| `Math.Convexity` | Existing finite negative-log Jensen, including nonnegative weights. |
| `Canonical.ThermodynamicChiralGraphCalculus` | Genuine finite likelihood IFT, despite its broader graph-calculus context. |
| `Canonical.JarzynskiQuantumThermodynamicsBridge` | Its named exponential is definitionally a scalar formula; it is not used as a fluctuation-expectation theorem. |

No existing full-matrix tensor-rank/pure-marginal erasure consumer,
block-uniform projective channel, or expectation/work consumer of the finite
IFT was found in these searches. No genuine full-operator Klein inequality or
thermodynamic optional-stopping owner was located. The smallest unresolved
implications are recorded below instead of being supplied as proof fields.

### Namespace-preserving trace-lemma move

`InfoGeometry.QuantumContext.MatrixStagePartialTrace.trace_mul_partialTraceSecondOp`
retains its exact statement, proof, and qualified name. Only its owner module
changes to `Quantum.FinitePartialTrace`, which now explicitly imports native
matrix Kronecker products. The declaration block's pre-move SHA256 is
`eace66d7be5af774f3f536bc2550612ab27c68ee551695ebb29de309fc5a0d60`.

The legacy tower owner already reaches the focused owner through
`FiniteAttentionCanonicalBridges`; its callers retain the same name and type.
Inspected consumers include the neighboring-stage adjoint theorem,
`FinitePairingReducedVacuum`, and the matrix-stage audit, product-density, and
selected-matrix modules. No forwarding alias or duplicate declaration is
created. The separate legacy tower source-closure attempt is blocked at its
preexisting `JordanKKTData → Architect` import; that regression boundary is
recorded rather than counted as a native pass.

## 4. Corrections and remaining mathematical debt

| Intake claim | Corrected contract and disposition |
|---|---|
| Exact erasure universally forces an infinite bath and divergent resources | The rank obstruction has an initially uncorrelated faithful finite bath hypothesis. Rank-deficient supplied auxiliaries are outside it. No time, energy, or control-complexity function is constructed. |
| A mixed joint density can be handled by its Schmidt decomposition | The supplied proof uses positivity and support of the full mixed matrix. An explicit pure-marginal product factorization remains separate from the sufficient rank bound. |
| Work lower bounds give exact stroke costs or attainable minima | Inequalities yield lower bounds. Saturation and physical attainability need additional arguments. A memory free-energy change is a physical state/Hamiltonian change. |
| Observational entropy grows monotonically at every later time | The channel is constructed. The actual operator-log entropy-gap identity, its support conventions and Klein inequality remain open in this change; no temporal monotonicity is asserted. |
| A causal bounded stopping rule alone supplies the corrected IFT | The finite likelihood IFT and its mean-work consumer are reused/proved. A process, filtration, appropriate likelihood correction, martingale and optional-stopping hypotheses remain separate obligations. |
| Reeb–Wolf, finite-time, finite-size and variance penalties can simply be added | Their physical model assumptions and compatibility need proof. This change supplies neither an additive universal resource budget nor a time-dependent dissipative dynamics. |
| All entropy notions and a proposed causal-poset synthesis are equivalent | The matrix, finite probability, thermodynamic, and order-theoretic carriers remain distinct. No narrative equivalence becomes a Lean axiom. |

### Source-grounded corrections

The published [de Oliveira Junior–Brask–Chaves tutorial](https://journals.aps.org/prxquantum/pdf/10.1103/phkv-wrsd)
contains a reversed relative-entropy logarithm in Eq. 22 and drops `log` from
the partition term before/within Eq. 66. With the usual conventions,
\(D(\sigma\|\rho)=\operatorname{Tr}\sigma(\log\sigma-\log\rho)\) and
\(S(\gamma)=\beta\operatorname{Tr}(\gamma H)+\log Z\).
For fixed nonzero entropy change and local dimension greater than one, the
displayed lower-bound function in Eq. 91 scales as \(\Theta(n^{-2})\).
The printed \(O(n^2)\) is a loose upper estimate, not the intended decay;
the lower bound alone does not establish the asymptotic cost of a protocol.
The tutorial itself distinguishes thermodynamic and von Neumann entropy and
uses an initially pure pointer in its finite CNOT example.

[Reeb–Wolf](https://arxiv.org/pdf/1306.4352), Proposition 5, gives a quantitative
minimum-eigenvalue obstruction. Its infinite-dimensional exact-erasure
example also uses unoccupied reservoir levels/formally infinite energies;
infinite dimension alone is insufficient. The general fixed-reference heat
ledger has both correlation and relative-entropy differences:

\[
\beta Q_B+\Delta S_S
=I(S:B)_\sigma-I(S:B)_\rho
+D(\sigma_B\|\gamma_B)-D(\rho_B\|\gamma_B).
\]

When the initial bath marginal equals \(\gamma_B\), the last term vanishes;
an initial product state also removes the initial mutual information. This
identity requires the actual spectral logarithms, support treatment, and
unitary entropy conservation. It is recorded as a target, not falsely
formalized by assuming its conclusion.

[Strasberg–Winter](https://journals.aps.org/prxquantum/pdf/10.1103/PRXQuantum.2.030202),
Lemma 5, compares later observational entropy with its initial value under the
preparation condition \(S_{\rm obs}(0)=S_{\rm vN}(\rho_0)\). It is not a
pairwise-in-time monotonicity statement. Their fluctuation discussion also
identifies the support condition needed to avoid absolute irreversibility.

[Manzano et al.](https://arxiv.org/pdf/2008.01630) derive the stopping-time
correction using a specific forward/backward likelihood term and martingale
arguments. The finite expectation theorem here supplies a useful final
implication once the appropriate pathwise relation has been established.

[Taranto et al.](https://journals.aps.org/prxquantum/abstract/10.1103/PRXQuantum.4.010332)
distinguish control models and resource tradeoffs, including finite energy
and time with unbounded control complexity. This does not justify a universal
conjunction requiring every resource to diverge.

[Guryanova–Friis–Huber](https://quantum-journal.org/papers/q-2020-01-13-222/pdf/)
give a universal-input faithful-measurement rank condition on the pointer.
An equal-dimensional pointer must be pure; a larger pointer can instead have
adequate rank deficiency. Supplying that state and thermally preparing it
are different resource questions.

[Boes–Ng–Wilming](https://journals.aps.org/prxquantum/pdf/10.1103/PRXQuantum.3.010325),
Box 2, derives the intake's single-shot variance correction for a specified
unital information-battery model with base-two entropy. The same discussion
allows that correction to disappear with an appropriate returned catalyst.
It is not a universal penalty, and conversion to natural-log units must also
rescale the qubit cost and variance.

## 5. Acceptance boundary

All promoted source statements contain complete proof terms/tactics. Source
review, source gates, native elaboration, axiom inspection and interpretation
review remain separate evidence stages. In particular:

- A passing text scan does not establish a Lean theorem.
- A native pass for the selected owners does not certify the root Lake package
  or the preexisting legacy tower closure.
- A native theorem proves its declared finite carrier and hypotheses; it does
  not establish the attachment's stronger physical synthesis.
- No dependency upgrade, custom axiom, proof hole, unsafe proof path, or
  surrogate diagonal operator is part of this change.

The precise commands, selected owners, evidence scope and unresolved native
status are maintained in [DEMON_ERASURE_VERIFICATION.md](DEMON_ERASURE_VERIFICATION.md).
