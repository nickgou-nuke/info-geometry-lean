# Centralizer localization and integral Weyl action: theorem contract

Status: `[accepted_limited_scope]` for the algebraic source verified below;
publication remains a draft with the disclosed repository-root blocker.
This contract records the actual carriers, hypotheses, declarations, and
boundaries of the restored change. **The current scoped run passed:** twenty
project modules, nine declaration owners, 488 audited declarations, and zero
warnings in all six new owners. Section 10 and the
[machine-readable validation record](CENTRALIZER_INTEGRAL_WEYL_VALIDATION.json)
bind that result to the exact source and toolchain. Historical reports are
provenance only.

The intake is the attachment `Pasted text(20261113-110355).txt`, preserved
as [the original intake](intake/centralizer-integral-weyl-20261113.txt), SHA256
`34314e4cd6c4486916673121d341bffe31f0892a6cf22bbb4354e4ee103b01a0`.
The recovery baseline is commit
`a392af178af1fe2bcba2ba39eb405700c6ee103c`. The restored work was integrated
onto main at `08c34e03f610b452e03422037949196dc7d92d6d`. The local source
verification commit is `9646e48664d2c65c8e3a8e59c09f322cb3c5f955`.
The published head is identified by the pull request metadata; its Lean
sources and maintained verification helpers are reconciled to the hashes
in the validation record. The pinned environment remains Lean
`leanprover/lean4:v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## 1. Intent and mathematical vocabulary

The formal target is a noncommutative algebraic chain: square-zero corner
operators, their Gram support, the precise coefficient domain of specified
fraction operations, an integral unitary on the idempotent-support locus, the
existing Peirce decomposition, and a concrete real matrix witness. Physical
interpretations in the intake are recorded as separate debt in Section 8.

Unless a statement explicitly adds more structure, the carrier is an arbitrary
`B` with `[Ring B] [StarRing B]`. Multiplication is the actual multiplication
of `B`. It is not assumed commutative, and no order, norm, topology,
division by two, or `NoZeroDivisors` instance is assumed.

The small existing
[RealBdGKreinChiralIdealBridge owner](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/RealBdGKreinChiralIdealBridge.lean)
owns the following polynomials. Its namespace starts with
`OperatorAlgebra.PeirceSpine`, without an `InfoGeometry` prefix.

| Mathematical notation | Existing Lean expression | Meaning |
|---|---|---|
| \(Q_+\) | `P N` | \(NN^*\) |
| \(Q_-\) | `Q N` | \(N^*N\) |
| \(V\) | `V N` | \(Q_++Q_-\) |
| \(\Sigma\) | `Sigma N` | \(Q_+-Q_-\) |
| \(J\) | `J N` | \(N-N^*\) |
| \(R\) | `1 - V N` | Residual support candidate |
| \(s\) | `1 + V N` | Gram denominator |
| \(u\) | `1 - V N + J N` | Integral Weyl polynomial |
| \(c\) | `1 - V N + (J N + J N)` | Cayley numerator |
| \(\Gamma\) | `InfoGeometry.Core.PeirceGrading.reflection (V N)` | \(V+V-1\) |

The original binary cut is denoted by lowercase \(p\), to distinguish it from
the existing definition `P N`. Its assumptions are `hp : p * p = p` and
`hps : star p = p`. The existing
[Basic](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/Basic.lean) and
[StarGrading](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/StarGrading.lean)
owners define
\(N=\operatorname{conePlus}(p,A)=pA(1-p)\), prove \(N^2=0\), and identify
its adjoint with the opposite corner. The generated coefficient ring is the
native `Subring.closure {p, N, star N}`; a subring already contains the identity
and the integer scalars.

The recurring additional hypotheses are:

| Hypothesis | Exact content | Where needed |
|---|---|---|
| `hF : ThreeSumStarFaithful B` | \(x^*x+y^*y+z^*z=0\Rightarrow x=y=z=0\) | Denominator cancellation, faithful embedding, and the support-to-regularity implication |
| `hN : N * N = 0` | Square-zero seed | Integral Gram identities, support commutation, and the Cayley numerator |
| `hV : V N * V N = V N` | Idempotent Gram support | Integral unitarity and the support Peirce decomposition |
| `hregular : N * star N * N = N` | Partial-isometry identity | Reused BdG normalization and the integral square formula; derived from `hF`, `hN`, `hV` |
| `[Algebra ℝ B]` | Real scalar algebra structure | The existing three spectral projectors and five adjoint-grade projectors |

“On shell” in this contract means precisely `hV`. “Off shell” means a result
does not require `hV`; it does not assert its negation. `ThreeSumStarFaithful`
is an explicit proposition supplied as a hypothesis, not a new axiom or an
implicit positivity assumption.

## 2. Causal owner map and reuse

The new modules have the following source-level responsibilities. An edge in
this table is a source import or an explicit theorem dependency, not a
physical analogy.

| New owner | Inputs reused | Added mathematical surface |
|---|---|---|
| [StarGramRegularity](../lean/InfoGeometry/OperatorAlgebra/StarGramRegularity.lean) | Native ring and star operations | Three-square faithfulness, properness, doubling cancellation, two-sided regularity of `1 + V` |
| [CentralPowerLocalization](../lean/InfoGeometry/OperatorAlgebra/CentralPowerLocalization.lean) | Native setoids, submonoids, and `OreLocalization` | Unconditional `DayRel` equivalence, exact raw-operation obstructions, central-powers fraction model and star structure |
| [IntegralWeyl](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/IntegralWeyl.lean) | StarGramRegularity, the small BdG owner, Core.PeirceGrading, native unitary conjugation | Gram-defect identity, support-to-regularity bridge, native ambient automorphism, square/fourth-power laws, weight reversal |
| [PeirceCentralizer](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/PeirceCentralizer.lean) | IntegralWeyl, Basic/StarGrading, native star centralizer, existing five-grade projectors | Centralizer membership, generated-ring inclusion, even-range identification, odd-range vanishing |
| [GramCentralLocalization](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GramCentralLocalization.lean) | CentralPowerLocalization and PeirceCentralizer | Faithful native centralizer localization, actual inverse denominator, localized Cayley unitary, on-shell comparison |
| [BalancedEightWitness](../lean/InfoGeometry/OperatorAlgebra/PeirceSpine/BalancedEightWitness.lean) | IntegralWeyl, CentralPowerLocalization, native real matrix and trace results | Explicit noncommutative 8 by 8 example, trace-conditioned cardinality, residual pairing, channels, and counterexamples |

The orthogonal supports and Steinberg/Weyl element remain owned by
`RealBdGKreinChiralIdealBridge`. The new code discharges its regularity
hypothesis; it does not duplicate the larger two-sheet development.
[Core.PeirceGrading](../lean/InfoGeometry/Core/PeirceGrading.lean) supplies the
even/odd projections, complementary ranges, and reflection. The real
specialization reuses
[TripotentPeirceProjectors](../lean/InfoGeometry/Physics/Algebra/TripotentPeirceProjectors.lean),
[TripotentLeftRightPeirceProjectors](../lean/InfoGeometry/Physics/Algebra/TripotentLeftRightPeirceProjectors.lean),
and
[TripotentFiveGradingDecomposition](../lean/InfoGeometry/Physics/Algebra/TripotentFiveGradingDecomposition.lean).
Its even-sum proof uses those projectors directly and does not import
`TripotentParity`, the supercharge development, or the singular-inverse branch
through that route.

The integral ambient automorphism does not depend on constructing a
localization. The localized Cayley fraction is a separate branch, with an
explicit comparison theorem on shell.

## 3. Faithfulness, DayRel, and the precise localization boundary

### 3.1 Cancellation from three-square faithfulness

`ThreeSumStarFaithful.proper` derives \(x^*x=0\Rightarrow x=0\).
`doubling_injective` derives injectivity of \(x\mapsto 2\mathbin{\bullet}x\).
For every \(N\), `one_add_gram_left_injective` and
`one_add_gram_right_injective` derive injectivity of left and right
multiplication by \(1+NN^*+N^*N\). These conclusions require neither
square-zero \(N\) nor idempotent \(V\). They hold in the entire ambient ring.

### 3.2 The equivalence relation exists without centrality

For any ring element \(s\), `DayRel s` on \(\mathbb N\times B\) is

\[
(k,x)\sim_s(\ell,y)
\quad\Longleftrightarrow\quad
\exists m\in\mathbb N,\quad s^m(s^\ell x)=s^m(s^k y).
\]

`dayRel_refl`, `dayRel_symm`, and `dayRel_trans` require no centrality or
regularity assumption. They define the native `daySetoid`. Thus the intake's
concern about transitivity outside the centralizer is resolved independently
of its concern about multiplication.

When left multiplication by \(s\) is injective,
`dayRel_iff_cross_eq` cancels the common power, and `dayRel_zero_iff` makes the
degree-zero map injective at the relation level.

The displayed raw operations are exactly

\[
\begin{aligned}
(k,x)+(\ell,y)&=(k+\ell,s^\ell x+s^k y),\\
(k,x)(\ell,y)&=(k+\ell,xy),\\
(k,x)^*&=(k,x^*).
\end{aligned}
\]

Under left regularity, `dayMul_identity_shift_iff` says that multiplying the
valid identity shift \((0,1)\sim_s(1,s)\) on the left by \((0,X)\) preserves
the relation exactly when \(sX=Xs\). `dayMul_congr_iff` upgrades this to
full congruence of this raw product on all pairs exactly when \(s\) commutes
with every coefficient. Under `star s = s`,
`dayStar_numerator_shift_iff` gives the corresponding exact obstruction for
componentwise star on \((0,X)\sim_s(1,sX)\).

For \(s=1+V\), `GramCentralLocalization.ambient_multiplication_iff` and
`ambient_star_iff` identify these conditions with
\(X\in C_B(V)\), using only `hF` in addition to the ambient star-ring
structure. In particular, these obstruction theorems do not need `hN` or
`hV`.

This yields a **maximality statement for the specified raw operations**:
if a coefficient subring contains \(s\) and its raw pair product is a
congruence under the inherited regularity hypothesis, every coefficient
must commute with \(s\). That subring is contained in \(C_B(V)\).
Conversely, the centralizer supports all the displayed operations.
This is a direct consequence of the congruence equivalence, not a
classification or uniqueness theorem for all noncommutative localizations,
Ore constructions, categorical colimits, or possible inverse-adjoining maps.

### 3.3 The ring carrier is native OreLocalization

If \(s\) is central in its coefficient ring, `centralPowersOreSet` supplies
the native Ore data for `Submonoid.powers s`; `RingLocalization` abbreviates
that native `OreLocalization`. `ofPair_eq_iff` identifies equality of its
fractions with `DayRel`. `quotientEquiv` is a plain equivalence between the
setoid quotient and that native localization; the ring structure used by the
development lives on the native localization, rather than on an additional
custom quotient carrier.

`ofPair_add` and `ofPair_mul` certify the raw formulas. For self-adjoint
\(s\), `localizationStarRing` and `degreeZero_star` certify the involution
and the star-preserving degree-zero map. `degreeZero_injective` requires
left regularity. Centrality alone does not assert faithful embedding.

## 4. Integral Weyl laws and the on-shell triad

Under `hN`, `support_commute_seed`, `support_commute_star_seed`, and
`support_commute_rotor` state that \(V\) commutes with \(N\), \(N^*\), and
\(J\). The reused BdG identity gives \(J^2=-V\). Consequently
`integral_gram_defects` states the two-sided identity

\[
u^*u=uu^*=1+(V^2-V).
\]

`integral_mem_unitary_iff` therefore identifies \(u\in\operatorname{unitary}(B)\)
with `hV`. This equivalence needs `hN`, but does not need `hF`.
`weylUnitary` bundles the on-shell element in the native `unitary B`, and
`weylAut` is Mathlib's native
\(B\simeq_{\mathbb Z}^{*\mathrm{alg}}B\), obtained by
`Unitary.conjStarAlgAut`. Its formula is \(X\mapsto uXu^*\) on every element
of the original ambient ring.

`regular_of_support_idempotent` uses `hF`, `hN`, and `hV` to derive
\(NN^*N=N\). With this bridge, the existing BdG results give the mutually
orthogonal self-adjoint idempotents \((Q_+,R,Q_-)\), their sum \(1\), and
\(\Sigma^2=V\). `PeirceCentralizer.sigma_tripotent` derives
\(\Sigma^3=\Sigma\), and `projZero_sigma` identifies the existing zero
projector with \(R\). These two bridge statements themselves do not require
a real algebra structure. No theorem here forces any of the three supports
to be nonzero.

`weyl_eq_steinberg` identifies the polynomial with the already owned
`W_Bog N` under `hN` and `hregular`. Under those same two hypotheses,
`integral_square` and `integral_fourth_power` state

\[
u^2=1-(V+V)=-\Gamma,\qquad u^4=1.
\]

For the automorphism API, `weylAut_sigma`, `weylAut_twice`, and
`weylAut_four_times` use `hF`, `hN`, and `hV`. They give

\[
\operatorname{Ad}_u(\Sigma)=-\Sigma,\qquad
\operatorname{Ad}_u^2(X)=\Gamma X\Gamma,\qquad
\operatorname{Ad}_u^4(X)=X.
\]

Thus the square of the action is the support-parity action. Calling the
ambient action an involution would be too strong: the matrix witness below
has a nonzero operator sent to its negative by the square. On the
centralizer, reflection conjugation is the identity.

`weylAut_reverses_weight` covers every integer commutator weight: if
\(\Sigma X-X\Sigma=k\mathbin{\bullet}X\), then the image satisfies the
same equation with \(-k\). This is an explicit algebraic weight statement.
It does not construct a new physical symmetry group or assume all weight
spaces are nonzero.

## 5. Centralizer, Peirce parity, and generated-ring starvation

`supportCentralizer N` is exactly the native
`StarSubalgebra.centralizer ℤ {V N}`. Since \(V^*=V\),
`mem_supportCentralizer` identifies membership with `Commute (V N) X`, and
`supportCentralizer_toSubring` identifies its underlying subring with the
ordinary native centralizer. The element `denominator N` is the actual
\(1+V\) inside this subtype; it is central there and self-adjoint without
assuming that \(V\) is central in \(B\).

Under `hV`, `mem_supportCentralizer_iff_even` identifies this centralizer
with the range of the existing even Peirce projection

\[
E_V(X)=VXV+(1-V)X(1-V).
\]

The complementary odd projection is
\(O_V(X)=VX(1-V)+(1-V)XV\). Its range meets the centralizer only in zero,
by `eq_zero_of_mem_supportCentralizer_of_mem_odd`. This conclusion uses
the existing complementary-submodule result and requires no faithfulness
or additive torsion hypothesis. The stronger reflection-fixed criterion
`reflection_fixed_iff_mem_supportCentralizer` uses `hF` to obtain the
needed doubling cancellation.

For `hp`, `hps`, and \(N=pA(1-p)\), `generated_le_centralizer` states

\[
\operatorname{Subring.closure}\{p,N,N^*\}\ \leq\ C_B(V).
\]

This inclusion is off shell. Adding `hV` gives `generated_odd_eq_zero`:
an element in that generated ring and the native odd Peirce range is zero.
It is a restriction on this generated coefficient ring. It does not say
that the ambient algebra has no odd operators.

For the real specialization, assume `[Algebra ℝ B]`, `hF`, `hN`, and
`hV`. Let \(\Pi_k\) denote the existing `fiveGradeProjector (Sigma N) k`
and let the grade spaces mean its native ranges. The statements
`even_support_eq_even_grades` and `commute_support_iff_even_grades` give

\[
E_V=\Pi_{-2}+\Pi_0+\Pi_2,\qquad
[V,X]=0\ \Longleftrightarrow\
\Pi_{-2}X+\Pi_0X+\Pi_2X=X.
\]

`centralizer_mem_odd_fiveGrade_eq_zero` and
`generated_odd_fiveGrade_eq_zero` give the corresponding zero intersections
with each of the native grades \(-1\) and \(1\). The proof uses existing
projector orthogonality and the existing five-grade decomposition. It does
not replace those ranges with a newly defined eigenspace carrier or add a
general converse eigenspace theorem. The older decomposition owner supplies
the forward commutator-eigenvalue interpretation of these ranges.

## 6. The faithful centralizer localization and Cayley comparison

`GramCentralLocalization.Localization N` instantiates the native central
powers construction inside `supportCentralizer N`. `embedding` is the
native degree-zero ring map, and `embedding_star` records its compatibility
with star. `embedding_injective` requires `hF`; the generated-ring
inclusion from Section 5 can therefore be followed by this faithful map.

`denominator_inverse` states that the fraction \([1,1]\) is a genuine
two-sided inverse of the embedded denominator. Under `hN`, both \(c\) and
\(u\) belong to the centralizer, and `cayleyNumerator_grams` gives

\[
c^*c=cc^*=s^2.
\]

Accordingly `cayleyFraction` is the actual fraction \([1,c]\), and
`cayleyFraction_mem_unitary` / `cayleyUnitary` give its native unitarity.
These statements require `hN`; they do not require `hF` or `hV`.
Faithfulness of the coefficient embedding is a separate conclusion under
`hF`.

On shell, `cayley_numerator_on_shell` gives \(su=c\) under `hregular`,
and `cayleyFraction_eq_integral_image` uses `hF`, `hN`, `hV` to identify
the localized Cayley fraction with the embedded integral element. The
off-shell fraction is not asserted to act on the original \(B\): such an
action would require a representation of the inverse denominator. On
shell, the integral unitary already acts on all of \(B\) through `weylAut`.

## 7. Exact scope of the 8 by 8 witness

The carrier is the full native ring
`Matrix (Fin 8) (Fin 8) ℝ`, with its native star, which is transpose over
the reals. It retains noncommutative matrix multiplication.
`matrix_threeSumStarFaithful` derives `hF` from native positive-semidefinite
trace results and the vanishing criterion for the trace of a Gram matrix.

With zero-based matrix units \(E_{ij}\), the actual definitions are

\[
p=E_{00}+E_{11}+E_{22}+E_{33},\qquad N=E_{04}+E_{15}.
\]

The source states self-adjointness and idempotence of \(p\), the corner
identity \(pN(1-p)=N\), square-zero \(N\), regularity \(NN^*N=N\), and
idempotence of \(V\). Its support and trace statements are:

| Element | Explicit support | Ordinary matrix trace |
|---|---|---|
| \(p\) | Coordinates \(0,1,2,3\) | \(4\) |
| \(Q_+\) | \(E_{00}+E_{11}\) | \(2\) |
| \(Q_-\) | \(E_{44}+E_{55}\) | \(2\) |
| \(V\) | Coordinates \(0,1,4,5\) | \(4\) |
| \(R\) | \(E_{22}+E_{33}+E_{66}+E_{77}\) | \(4\) |
| \(pR\) | \(E_{22}+E_{33}\) | \(2\) |
| \((1-p)R\) | Remaining two residual coordinates | \(2\) |
| \(\Gamma=2V-1\) | Difference of support and residual projectors | \(0\) |

These are explicit support and ordinary-trace theorems. The change does
not add a general rank-classification theorem, a Clifford tensor-product
isomorphism, or an anomaly invariant.

### 7.1 Residual pairing and retained channels

The explicit residual pairing is

\[
K=E_{23}-E_{32}+E_{67}-E_{76}.
\]

`residualPairing_skew`, `residualPairing_square`, and
`residualPairing_supported` give \(K^*=-K\), \(K^2=-R\), and
\(RK=K=KR\). Here \(R\) is the identity of the residual corner, not the
identity of the ambient matrix ring. `residualPairing_kernel` says that
\(RX=X\) and \(KX=0\) imply \(X=0\). This is the exact supported-kernel
statement; no physical pairing dynamics is bundled with it.

The retained operators are

\[
U=E_{02},\qquad L=E_{64},\qquad G=E_{26}.
\]

The source gives \(U\ne0\), \(L\ne0\), \(pUp=U\),
\((1-p)L(1-p)=L\), and
\([\Sigma,U]=U\), \([\Sigma,L]=L\). Thus these particular binary-even
operators have odd emergent commutator weight. It also gives \(RGR=G\),
\((U+L)^2=0\), and

\[
UGL=E_{04}\ne0,\qquad UG\ne GU.
\]

This is an explicit nonzero ordered three-factor path. It does not assert
surjectivity of a grade bracket, a Morita equivalence, or that all ambient
odd channels arise from binary-diagonal operators.

### 7.2 Counterexamples to two overstrong readings

The witness has \(sU=2U\) and \(Us=U\), hence \([s,U]\ne0\).
`day_multiplication_failure` and `day_star_failure` instantiate the exact
raw-operation obstructions with this matrix. They do not refute existence
of the `DayRel` equivalence relation.

The existing Weyl element sends \(U\) to \(-E_{42}\) and \(E_{42}\) to
\(U\). Both the explicit conjugation statements and
`native_weyl_action_twice_upperChannel` give
\(\operatorname{Ad}_u^2(U)=-U\ne U\). This witnesses nontrivial ambient
odd parity and excludes a blanket order-two claim for the Weyl action.

### 7.3 Exactly what forces cardinality eight

`card_eq_eight_of_trace_balance` is stated for any finite index type
\(\iota\) and any \(N\in\operatorname{Matrix}(\iota,\iota,\mathbb R)\).
Its hypotheses are exactly

\[
\operatorname{tr}(Q_+)=2,\qquad
\operatorname{tr}(Q_-)=2,\qquad
\operatorname{tr}(2V-1)=0.
\]

Its conclusion is `Fintype.card ι = 8`, by trace arithmetic. The theorem
does not require square-zero or support-idempotence assumptions. In
particular, the two trace values are premises, not consequences of the
abstract square-zero construction. Trace balance by itself does not force
dimension eight. The theorem neither selects a unique representation nor
establishes physical Weyl-anomaly cancellation.

## 8. Intake claim ledger and adjacent debt

The following labels describe source scope; the fresh validation status
for all theorem-bearing rows is recorded separately in Section 10.

| Intake component | Disposition | Exact boundary |
|---|---|---|
| K0: three-sum faithfulness | `[bucket_2_conditional]` generically; explicit matrix derivation | Hypothesis in arbitrary star rings; derived in the full real 8 by 8 matrix witness |
| K1: binary corner and generated algebra | Existing owner reuse plus source implementation | Native corner identities; native generated subring lies in the Gram centralizer off shell |
| K2: Day equivalence and algebra laws | Corrected source implementation | Equivalence is unconditional; the displayed multiplication/star obstruction is centralizer-specific under regularity |
| K3: Gram defect and Cayley element | Source implementation | Integral Gram defect, exact unitarity criterion, native localized Cayley unitary, and on-shell comparison |
| K4: triad and Weyl reflection | `[bucket_2_conditional]` with corrected action law | Partial-isometry bridge and reused triad; \(u^2=-\Gamma\), \(\operatorname{Ad}_u^2\) is parity, fourth action is identity |
| K5: five grading and starvation | `[bucket_2_conditional]` | Native real projector ranges; generated-ring odd intersections vanish; ambient odd operators remain possible |
| K6: eight-dimensional balance | Explicit finite witness and conditional cardinality | Fixed trace profile forces cardinality eight; no uniqueness of algebra, cut, representation, or Clifford realization |
| K7: residual channels and pairing | Limited finite statements; broader claims `[bucket_3_open_debt]` | Supported skew pairing, explicit channels, and one nonzero bridged product; no general Morita/spacetime/supersymmetry/Andreev theorem |
| K8: analytic and physical consequences | `[bucket_3_open_debt]` | No new completely positive evolution, strict Kadison–Schwarz leakage, Fisher–Rao diffusion, KMS equilibrium, gravity, or Goldstone-photon theorem |
| K9: master synthesis/equivalence | `[bucket_3_open_debt]` | The listed algebraic implications do not establish the intake's universal equivalence or unique physical realization |

In particular, there is no claim here that a nonzero residual sector, a
nonzero odd sector, or strictly positive leakage follows for every seed.
The explicit witness supplies selected nonzero operators. Extending the
finite statements to categorical, analytic, or physical claims requires
named carriers, maps, and additional theorems; vocabulary in the intake
does not provide them.

## 9. Recovery and provenance record

The task runtime reset removed the earlier temporary checkout and evidence
artifacts. Four of the six new code files were recovered byte for byte
against their recorded final SHA256 values:

| New owner | Exact recovered SHA256 |
|---|---|
| `CentralPowerLocalization.lean` | `f078908ebba66dae57d0dce3993e79dd62c74f8869376183faa46ecbb12d085e` |
| `PeirceCentralizer.lean` | `83b8e6fc07ed0c2a24a494bc2284758e0a3322030eafd73d220a868588ff570f` |
| `GramCentralLocalization.lean` | `d272f8c2d05359037999249cf1470f6cd98c8d6c081ce042fc084cfaee1cd054` |
| `BalancedEightWitness.lean` | `e8d834870e5be1bd99a8abbb408acb03ae94dc21162ccdddd422cb1d0b3b74c2` |

`StarGramRegularity.lean` was reconstructed as a complete file with its
retained proof tail copied literally. It is not claimed to match the
historical whole-file bytes. `IntegralWeyl.lean` was reconstructed from the
retained contract and consumers; its full historical source was not
recoverable. The integrated reconstruction includes `coe_weylUnitary`.
Both and their consumers passed the fresh validation recorded in Section 10.

The three edited pre-existing projector files were also recovered against
their historical hashes at the recovery baseline. Integration with newer
main preserved its three additional star-section theorems in
`TripotentPeirceProjectors`; that final integrated file has a different hash
from its historical recovery. The current source hashes are recorded
independently in the validation record. “Four exact files” counts the six
new owners; it does not ignore those three existing-owner recoveries.

The focused workflow was reconstructed from the exact original workflow
and the retained final requirements. This document is reconstructed anew.
Neither is represented as a byte-exact recovery of the historical final
version. No claim is made that the old integrated Git tree or its commit
has been retained.

The historical proof run identified as `16601ece` was reported to have
passed. Its evidence artifacts are no longer present after the reset.
That history is provenance only: it is **not a current verification
certificate**, and it does not establish that the reconstructed files or
the current-main integration compile.

## 10. Current validation and draft publication boundary

The final accepted local source snapshot is
`9646e48664d2c65c8e3a8e59c09f322cb3c5f955`, integrated on
`08c34e03f610b452e03422037949196dc7d92d6d`. All theorem-bearing source
files and the four maintained checker/helper files match their committed
Git blobs and the copied compiler inputs. The publication step also
reconciles those same hashes against the published tree.

### 10.1 Commands and results

The native check used the unchanged maintained command, from the repository
root, with one `--target` for each of the nine owners listed below:

```sh
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/64554963d837/mathlib-4.34.1 \
  --lean /workspace/scratch/64554963d837/lean-runtime/bin/lean \
  --output /workspace/scratch/64554963d837/verification \
  --incremental \
  --target InfoGeometry.OperatorAlgebra.StarGramRegularity \
  --target InfoGeometry.OperatorAlgebra.CentralPowerLocalization \
  --target InfoGeometry.OperatorAlgebra.PeirceSpine.IntegralWeyl \
  --target InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceCentralizer \
  --target InfoGeometry.OperatorAlgebra.PeirceSpine.GramCentralLocalization \
  --target InfoGeometry.OperatorAlgebra.PeirceSpine.BalancedEightWitness \
  --target InfoGeometry.Physics.Algebra.TripotentPeirceProjectors \
  --target InfoGeometry.Physics.Algebra.TripotentLeftRightPeirceProjectors \
  --target InfoGeometry.Physics.Algebra.TripotentFiveGradingDecomposition
```

It exited zero with `PASSED`. The initial run compiled all twenty project
modules from this session's restored checkout. After removing one unused
simplification argument, the final run compiled the four affected owners
again and reused sixteen outputs whose source, dependency, compiler, and
artifact hashes matched. No project artifact from the lost historical run
was available or reused. The native audit ran again for all nine owners.

| Check | Current observed result |
|---|---|
| Pinned environment | Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; pins unchanged |
| Native imports | Thirty direct Mathlib import roots; pinned native cache retrieval succeeded; actual project closure contains twenty modules |
| Strict source gates | `placeholder_audit.py --strict --root FILE --json-out REPORT` on each owner and `opengauss_screener.py --strict --json` on all nine: passed |
| Semantic error gate | `semantic_vacuity_gate.py` on all nine with `--fail-on error`: passed, zero errors, 26 advisory trivial-surface findings retained |
| Scoped kernel compilation | All twenty project modules returned zero |
| Native owner audit | 488 declarations, including private/generated declarations and instances; no selected unsafe or partial declaration; only `propext`, `Classical.choice`, and `Quot.sound` in the axiom closure |
| Six new owners | Zero compiler warnings in every owner |
| Three existing selected owners | Seven warnings in `TripotentPeirceProjectors`; zero in the other two; the seventh comes from the preserved upstream star section |
| Other imported project owners | 65 warnings retained separately: PeirceDecomposition 1, TripotentAdjointDerivation 4, TKKConformalClosure 26, SuperTKKConformalClosure 34 |
| Staged hook | Installed tracked hooks; actual pre-commit executions printed `proof_proxy_staged_gate: ok` for the restoration and proof cleanup commits |
| Independent scope review | Restored mathematics and upstream integration reviewed independently; no mathematical defect found |
| Workflow syntax | YAML parsed; all seven shell blocks and all six embedded Python blocks syntax checked; this is not a claim that GitHub Actions has completed |

The measured owner counts are:

| Owner | Audited declarations |
|---|---:|
| StarGramRegularity | 8 |
| CentralPowerLocalization | 66 |
| IntegralWeyl | 34 |
| PeirceCentralizer | 32 |
| GramCentralLocalization | 27 |
| BalancedEightWitness | 81 |
| TripotentPeirceProjectors | 53 |
| TripotentLeftRightPeirceProjectors | 89 |
| TripotentFiveGradingDecomposition | 98 |
| **Total** | **488** |

The validation JSON contains the complete source SHA256 map, dependency
fingerprints, compiled artifact hashes, helper hashes, current warning
counts, and evidence-file digests. Those are results of the current run;
the historical total of 486 has not been reused as a current certificate.

### 10.2 Repository-root blocker and authorized draft exception

At that same source commit, the maintained preflight

```sh
python3 tools/infra/ci_bootstrap.py paths --root .
```

exited one. `HomotopyHypothesis` lacks its recorded `lakefile.lean` and
tracked path provenance; `Atlas` lacks its recorded `lakefile.toml` and
tracked path provenance. The `GIFT` gitlink is pinned at
`e6f3c3ac2140c2324fb2ae029c32233e73aa5e92` but is uninitialized and lacks
its package configuration. `InfoGeometryCore` passed this availability and
provenance check. The complete JSON diagnostics are preserved in the
validation record.

The root Lake build and complete pre-push gate have **not passed**. No root
success is inferred from the scoped check. The user explicitly authorized
draft publication with this disclosed blocker. No dependency pin was
changed, no stub package was inserted, and no proof checker or hook was
altered. The draft remains a reviewable algebraic change with this
integration boundary visible.

### 10.3 Reproducible CI scope

The [focused workflow](../.github/workflows/centralizer-integral-weyl.yml)
fetches the exact public source revision and pinned Mathlib source, computes
the actual import closure, applies source gates to all nine owners, freshly
compiles the project closure, and audits all nine declaration owners. It
requires zero warnings in the six new owners and records existing-owner
warnings separately. It reconciles current, Git, copied-source, helper, and
compiled artifact hashes, and uploads the complete evidence directory on
success or failure. Unlike the local final pass, CI rejects reused project
compilation results. Its actual execution status is reported by the pull
request checks, not by this document.
