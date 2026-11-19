# Peirce round trips: claim review and theorem contract

## Provenance and review scope

Source: the supplied `Pasted text(20261116-141041).txt`, sections I–V and deductions 1–8.
Its SHA-256 is `703e4726d3804a8c5d902eb6aa07668e29e38021c46c16152fdcb22dd8762934`.
The repository source inspected for this review was based at
`08c34e03f610b452e03422037949196dc7d92d6d` in
`nickgou-nuke/info-geometry-lean`.

This document separates exact algebraic statements, additional hypotheses,
countermodels, and interpretations. The review makes no psychological
attributions. Its source-level assessment is not a replacement for the build,
axiom audit, and final semantic acceptance of the corresponding Lean changes.
Existing declarations listed below were read at source level; their inclusion
here is not a claim that the entire repository was rebuilt in this task.

## 1. Canonical carrier and notation

Let `R` be an arbitrary associative unital ring and let `p : R` satisfy
`p * p = p`. Put `q = 1 - p` and `j = p - q`. These data give

\[
q^2=q,\quad pq=qp=0,\quad p+q=1,\quad j^2=1.
\]

For an operator `m`, its four Peirce components are

\[
k=pmp,\qquad u=pmq,\qquad v=qmp,\qquad d=qmq,
\qquad m=k+u+v+d.
\]

The upper and lower components may also come from independently chosen
operators, `u=paq` and `v=qcp`. Multiplication is composition with the
rightmost factor applied first. It is not commutative. Then

\[
u^2=v^2=0,\qquad uv\in pRp,\qquad vu\in qRq.
\]

Define the round-trip sum and difference by

\[
g=uv+vu,\qquad t=uv-vu.
\]

These are the source's `\mathfrak G` and `\mathfrak T`. The repository's
Peirce spine calls them `genV` and `genSig`; its grading involution is `invS`.
This notation map matters because the source also uses `J` and `Σ` for
different objects.

No Hilbert space, positivity, topology, probability law, physical causality,
or empirical interpretation follows just from these ring assumptions.
For an orthogonal decomposition, an inner product and a self-adjoint
projection must be supplied. An algebraic complementary decomposition alone
does not mean orthogonality.

## 2. Atomic claim ledger

| ID | Source claim | Mathematical disposition | Exact correction or condition |
| --- | --- | --- | --- |
| C01 | A binary cut gives four operator blocks. | Owner-backed algebra. | Use an idempotent and its complement in an associative ring, or an actual direct sum of modules. |
| C02 | The involution `J²=1` is itself non-reversible. | Countermodel to the wording. | `J` is invertible with inverse `J`; information loss belongs to discarding a nontrivial complementary component. |
| C03 | Opposite off-diagonal blocks square to zero. | Owner-backed algebra. | Follows from `pq=qp=0`. |
| C04 | `t=jg`, hence `t=0` iff `g=0`. | Owner-backed algebra. | Also `g=0` iff `uv=0` and `vu=0`; it does not imply `u=0` or `v=0`. |
| C05 | `uv≠0` forces a nonempty nonzero spectrum. | Countermodel found. | A nonzero nilpotent round trip has spectrum `{0}`. |
| C06 | The partners have the same nonzero eigenvalues. | Owner-backed conditional statement. | A nonzero eigenvalue gives an explicit equivalence of eigenspaces; it does not assert that any such eigenvalue exists. |
| C07 | The defect of the compressed operator equals the cross product. | Sign and operation distinction required. | Compression of the ambient defect differs from the defect after compression by `uv`. If `k²=k`, then `p(m²-m)p=uv`, while `k²-k=0`. |
| C08 | Operator rings contradict Lean's proof irrelevance, exchange, or contraction. | False as a general claim. | Operators are data in `Type`; proofs of propositions are in `Prop`. Exchange of contexts does not imply commuting compositions. |
| C09 | Nonzero partial isometries form a composable proof system. | Countermodel found. | Their products can be zero or fail to be partial isometries. Supply compatible supports or another proved composition condition. |
| C10 | Equal nonzero partner spectra canonically produce an adjoint pair. | Unsupported implication. | An adjoint relation or a specified polar decomposition is additional structure. Equal eigenvalue sets do not determine singular values, adjoints, or a unique calibration. |
| C11 | A partial isometry gives an idempotent support and a supported rotation. | Conditional algebra, with an analytic extension. | Use `vv*v=v`, the actual star structure, and real scalar action; an exponential identity needs a suitable normed complete algebra. |
| C12 | `θ=π` automatically proves a physical spinorial `2π` holonomy. | Open representation/geometry claim. | The algebra proves a minus sign on the support at parameter `π` and identity at `2π`. A physical angle and a Spin-to-SO covering map require separate definitions and compatibility. |
| C13 | The defect is nonzero at every later stage and in a colimit. | Unsupported and false without added hypotheses. | Specify the stage objects, bonding maps, compatibility, and injectivity/nonvanishing assumptions. Arbitrary defect iteration can terminate. |
| C14 | The support complement is automatically a stochastic nilpotent/Drazin remainder. | Countermodel found. | A projector split is not a spectral noise filter. Invariance requires commutation with the operator being decomposed; nilpotence is a further hypothesis. |
| C15 | The displayed 15-node graph is a graded bounded poset whose terminal join yields a unique substantive synthesis. | Partly combinatorial, partly false or interpretive. | It is a bounded acyclic poset with strictly increasing levels, and its specified terminal join exists. It is not graded. A chosen terminal node establishes no uniqueness theorem about its interpretation. |
| C16 | Every Peirce corner `eRf` is a projective bimodule. | Additional hypothesis required. | It is naturally an `eRe`–`fRf` bimodule. Projectivity over the corner rings does not follow from idempotency alone. |

## 3. Exact derivations and countermodels

### 3.1 Sum and commutator have the same vanishing condition

The corner identities give

\[
j(uv)=uv,\qquad j(vu)=-vu,
\]

so `jg=t`. Since `j²=1`, also `jt=g`. Thus `t=0` iff `g=0`.
Multiplying `g=0` by `p` isolates `uv=0`; multiplying by `q` isolates
`vu=0`. The converse follows by addition.

The strongest unconditional conclusion is therefore

\[
t=0\iff g=0\iff(uv=0\ \text{and}\ vu=0).
\]

The individual cross maps need not vanish. An existing full `4 × 4` real
matrix countermodel in `PeirceSpine/PeirceOverlapCounterexamples.lean` uses
zero-based matrix units

\[
p=E_{00}+E_{33},\quad u=E_{01},\quad v=E_{23}.
\]

Both `u` and `v` are nonzero opposite corners, while `uv=vu=0`. The cut
also fails to commute with the upper map. This is not a scalar surrogate.

### 3.2 Nonzero round trips can have only zero in their spectrum

A two-dimensional partner model is `A=I₂`, `B=N`, where

\[
N=\begin{pmatrix}0&1\\0&0\end{pmatrix},\qquad N\ne0,\quad N^2=0.
\]

Then `AB=BA=N`, whose algebraic spectrum is `{0}` over either `ℝ` or `ℂ`.
To retain the opposite-corner structure in one genuinely noncommutative
operator algebra, the implementation candidate uses the full `M₄(ℝ)`:

\[
p=E_{00}+E_{11},\qquad
u=E_{02}+E_{13},\qquad
v=E_{21}.
\]

Its ordered products are

\[
uv=E_{01}\ne0,\qquad vu=E_{23}\ne0,\qquad uv\ne vu.
\]

Both products square to zero. Their sum and difference are likewise nonzero
and square-zero. Consequently all four operators have spectrum `{0}`.
This directly refutes the source's inference under its own nonzero
round-trip premise.

The generic fact used is stronger than the matrix example: if `a` is
nilpotent in a nontrivial algebra over a field, then its algebraic spectrum
is exactly `{0}`. For `λ≠0` and `aⁿ=0`, an inverse of `λ·1-a` is the finite
geometric sum

\[
\sum_{k=0}^{n-1}\lambda^{-k-1}a^k.
\]

Conversely a nilpotent element cannot be a unit in a nontrivial ring, so
zero belongs to the spectrum. The candidate proof uses Mathlib's native
spectrum and power spectral mapping, not a separately invented spectrum.

The correct partner theorem remains valuable. For `A:X→Y`, `B:Y→X` and
`λ≠0`,

\[
A:E_\lambda(BA)\longrightarrow E_\lambda(AB)
\]

is a linear equivalence, with inverse `λ⁻¹B`. Indeed,
`AB(Ax)=A(BAx)=λAx`, and `λ⁻¹BAx=x`. These statements hold for unequal
and infinite ambient dimensions. They are already implemented as
`PartnerEigenspaces.nonzeroEigenspaceEquiv`; the unit-eigenvalue version
`unitEigenspaceEquiv` works over a commutative ring.

For two elements of one algebra, Mathlib already owns
`spectrum.nonzero_mul_comm`. Equality of the nonzero spectra does not
establish their nonemptiness. Transport of point eigenvectors alone also
does not prove full spectral equality for arbitrary infinite-dimensional
bounded operators; the algebraic resolvent argument is the relevant
additional proof.

### 3.3 Compression of a defect is not the defect of a compression

With `δ(x)=x²-x`, direct multiplication gives

\[
p\delta(m)p=\delta(pmp)+pm(1-p)mp.
\]

Equivalently,

\[
\delta(pmp)=p\delta(m)p-pm(1-p)mp.
\]

When `k=pmp` is idempotent, the first formula reduces to
`pδ(m)p=uv`. It does not say `δ(k)=uv`; that would contradict `δ(k)=0`
whenever the round trip is nonzero.

The existing owner `Core/PeirceCompressionDefect.lean` already proves
`compression_mul_defect`, `compression_square_defect`,
`defect_compression`, and `defect_compression_peirce_transfer`.
`OperatorAlgebra/PeirceDefectBridge.lean` also exposes the same distinction
as `peirce11_idempotencyDefect_sub` and its lower-corner counterpart.

No conclusion about a proof checker's semantic reliability follows from
this operator identity unless the checker and the interpretation maps have
been explicitly modelled and linked to these operators.

### 3.4 Partial isometries require a composition law

In a star ring, use the explicit algebraic condition

\[
vv^*v=v.
\]

It implies that `e=v*v` and `f=vv*` are self-adjoint idempotents and that
`ve=v=fv`. These facts require no commutativity assumption on the ambient
ring. They do not make arbitrary products of partial isometries partial
isometries.

For a concrete real countermodel, let

\[
P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
Q=\tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix}.
\]

Both are nonzero self-adjoint idempotents, hence partial isometries.
For `W=PQ`,

\[
WW^*W=PQPQ=\tfrac12PQ=\tfrac12W\ne W.
\]

Thus the class is not closed under multiplication. Taking the orthogonal
projections `E₀₀` and `E₁₁` additionally shows that a product of two
nonzero partial isometries can be zero. Excluding zero morphisms does not
repair either failure.

A sufficient compositional condition is that the adjacent supports
commute. If `v` and `w` are partial isometries and

\[
(vv^*)(w^*w)=(w^*w)(vv^*),
\]

then

\[
(wv)(wv)^*(wv)
=w(vv^*)(w^*w)v
=w(w^*w)(vv^*)v
=wv.
\]

More precisely, the added algebraic theorem retains the complete residual:

\[
(wv)(wv)^*(wv)-wv
=w\bigl[(vv^*),(w^*w)\bigr]v.
\]

Hence `wv` is a partial isometry exactly when this sandwiched commutator
vanishes. Over an arbitrary star ring, the theorem does not cancel `w`
and `v` or replace this exact condition by an unproved equivalence with
commutation of the supports.

The matched-support case `vv*=w*w` gives the usual composition between
specified support projections. The repository already proves its endpoint
projection calculation in `RealProjectionMurrayVonNeumann.mvn_trans`.
A reusable partial-isometry criterion and explicit failure countermodels
are useful additions; a duplicate existential equivalence theorem is not
needed.

The proposed native `Categorical/PartialIsometryGroupoid.lean` makes this
repair structural: objects are Mathlib star projections; an arrow is an
actual partial-isometry element with the specified source and range;
composition is ordered ambient multiplication; and the adjoint is the
inverse. It retains the zero projection, whose identity is zero. Nonzero
supports force their outgoing arrows to be nonzero, so matched composition
does not need an artificial exclusion of zero from all hom-spaces. This
constructs a groupoid in Lean's ordinary type theory without asserting that
its arrows are logical proofs.

Polar decomposition is an additional construction. For a bounded operator
on Hilbert spaces, canonical uniqueness of the polar partial isometry uses
its prescribed initial support, equivalently the kernel condition. An
arbitrary algebra need not contain its polar factor. Equality of the
nonzero spectra of `AB` and `BA` supplies none of this data and does not
force `B=A*`.

### 3.5 Supported rotations and the exact angle statement

For a specified partial isometry `V:T→S` with adjoint `V*`, form

\[
\Omega=\begin{pmatrix}0&V^*\\-V&0\end{pmatrix},\qquad
P_c=\begin{pmatrix}V^*V&0\\0&VV^*\end{pmatrix}.
\]

The partial-isometry equations imply

\[
P_c^2=P_c,\quad \Omega^2=-P_c,\quad
P_c\Omega=\Omega P_c=\Omega,\quad \Omega^*=-\Omega.
\]

With real scalar multiplication, define

\[
R(\theta)=(1-P_c)+\cos\theta\,P_c+\sin\theta\,\Omega.
\]

The displayed polynomial relations and the trigonometric addition formulas
give `R(θ+φ)=R(θ)R(φ)`, `R(0)=1`, and `R(-θ)=R(θ)*`. In particular,

\[
R(\pi)=1-2P_c,\quad R(\pi)P_c=-P_c,\quad
R(\pi)(1-P_c)=1-P_c,\quad R(2\pi)=1.
\]

These facts do not use the source's proposed transfinite obstruction.
Identifying `R(θ)` with an analytic exponential requires an appropriate
complete normed algebra and the corresponding convergent-series theorem.
Interpreting a parameter `π` as a physical rotation of `2π` requires a
specified double-cover representation. In the displayed operator parameter,
`π` is a half turn and `2π` is a full period. On vectors having both core
and complementary components, `1-2P_c` is not even a global scalar phase.

Existing owner `Core/PeirceRotor.lean` gives the supported polynomial rotor
and its multiplication and inverse laws as `phaseRotor_formula`,
`phaseRotor_mul`, `phaseRotor_inverse`, and `phaseRotorUnit`, from the
explicit `IsDualSeedPair` equations. `Canonical/ReflexiveRotorRealTime.lean`
evaluates the actual real sine/cosine curve and proves its generator
derivative. Its `hasDerivAt_realRotor` is an analytic derivative theorem in
a normed real algebra; the owner explicitly does not claim equality with
an exponential. These are positive reusable results, not missing
infrastructure.

### 3.6 Support decomposition does not identify a Drazin remainder

An idempotent endomorphism `P` gives the canonical direct sum

\[
E=\operatorname{range}P\oplus\ker P,
\qquad\ker P=\operatorname{range}(1-P).
\]

For an independent endomorphism `Γ`, both summands are invariant exactly
when `ΓP=PΓ`. One direction follows by applying the commuting equation to
vectors in the range and kernel. Conversely, write each vector as
`Px+(1-P)x`; preservation of the two summands makes the off-diagonal terms
zero and yields the commuting equation.

Commutation still does not imply nilpotence on the complementary summand.
For example `P=diag(1,0)` and `Γ=diag(1,2)` commute, while the restriction
of `Γ` to `ker P` is multiplication by `2`, not nilpotent. Taking a swap
matrix for `Γ` instead shows that an arbitrary `Γ` need not preserve either
summand at all.

A Drazin decomposition of `Γ` needs an invariant split with an invertible
restriction on one component and a nilpotent restriction on the other.
A statistical signal/noise split additionally needs a specified statistical
model and a validated selection rule. Neither assertion follows from
`P²=P` or from `VV*V=V` alone.

The repository already contains the relevant genuine Drazin constructor:
`Canonical/Drazin.lean`, `IsDrazinInverse.of_core_nilpotent_split`. Its
inputs include `a=u+n`, zero cross-products, a commuting block inverse `d`,
the inverse identities `udu=u` and `dud=d`, annihilation of the nilpotent
block by `d` on both sides, and `n^(m+1)=0`. It derives the Drazin equations.
The gap in the intake is the construction of those hypotheses for its
particular `Γ` and projector, not the absence of a Drazin theory in the
codebase.

### 3.7 Defect persistence and colimits need explicit maps

The source uses the notation `A_n ↪ A_(n+1)` without defining the stage
objects, their maps, or an injectivity theorem. A defect operator is an
element of an algebra; it is not automatically an object of a category
that can be placed in a direct system.

If a directed system of modules has injective bonding maps, a nonzero
element survives under the canonical map into its direct limit. A proof
can use native `Module.DirectLimit.of.zero_exact`: an element that becomes
zero is already sent to zero at some later stage, contradicting injectivity.
Without injective maps, nonzero module stages can all collapse: use a
constant nonzero vector space with zero transitions between different
indices. This is a module counterexample; it is not a claim about unital
ring homomorphisms sending `1` to `0`.

For associative rings, the existing
`OperatorAlgebra/PeirceCoupling/CartanDirectLimit.lean` uses Mathlib's actual
noncommutative `DirectLimit` quotient. Its `of_injective` proves faithfulness
from injective bonding maps, `support_of_ne_zero` proves survival of a
specified dual-seed support, and `lift_exists_unique` supplies the universal
property. These statements are available for a properly specified system;
the source does not identify its informal sequence with that system or
construct the required injective maps.

Nor does nonzero initial data imply perpetual nonzero defect iteration.
For a nonzero projection `P`, `δ(P)=0`. The repository's actual
`PeirceSpine/ReflexiveObserver.lean` already distinguishes models:
`observer_matrix_meta_reflection_collapse` gives terminating defect towers,
whereas `observer_matrix_metric_tower_ne_zero` gives an explicit persistent
matrix model. Neither behavior is universal under the bare ring hypotheses.

No cochain complex, differential, cohomology class, or obstruction map is
defined in the source for `A_ω`. The description as a nonzero cohomological
obstruction is therefore an open specification, not a corollary of the
finite block identities.

### 3.8 The logical and categorical distinctions

Lean's [proof irrelevance](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/)
identifies two proofs of the same proposition.
It does not identify distinct operators whose data live in `Type`. A
zero linear map is an element of a hom-space; it is not an inhabitant of
the proposition `False`. A function duplicating a classical description
of an operator is not a physical operation cloning an unknown quantum
state. Exchanging variables in a context does not exchange factors in a
sequential composition.

One can construct an inconsistent interpretation by explicitly assuming a
decoding map that turns every zero morphism into a proof of every
proposition, including `False`. The contradiction comes from that decoding
assumption. It is not a contradiction in encoding a noncommutative algebra
within dependent type theory. Likewise, faithfully encoding a nontrivial
data type into a proof-irrelevant proposition is impossible, but this
limited obstruction says nothing against keeping the data in `Type`.

A proof checker verifies a supplied derivation. This must not be confused
with a decision procedure for the existence of proofs of arbitrary
propositions. Formal checking also does not itself establish how measured
physical data correspond to a chosen mathematical model.

Finally, `eRf` is naturally a bimodule over `eRe` and `fRf`, but automatic
projectivity over these corner rings is overstrong. For example an upper
triangular ring with diagonal rings `ℤ/2ℤ` and `ℤ` and off-diagonal module
`ℤ/2ℤ` has such a corner whose right `ℤ`-module is not projective.
Projectivity, fullness, and any claimed Morita equivalence need their own
hypotheses and proofs.

### 3.9 What the displayed dependency poset actually proves

Every listed arrow increases the supplied level, so its transitive closure
is irreflexive and acyclic. The displayed predecessors are incomparable;
the chosen initial and final nodes give bottom and top. These are
combinatorial facts about the graph as specified.

It is not a graded poset. It has maximal chains

1. `Δ → T → K → B → H → Ξ`, with five edges;
2. `Δ → T → Π → G → B → H → Ξ`, with six edges.

All arrows in these two chains are listed covers. Thus no rank assigning
one-step increments to covers can give both chains the same endpoint rank.
The source's level is a strictly increasing topological level, not a rank
function for a graded poset.

As an additional boundary, the poset is not a lattice: `T` and `S` have two incomparable minimal upper
bounds, `Π` and `Σ`, so their join does not exist. The particular join
`H∨D=Ξ` does hold in this chosen graph, but its existence follows from
the chosen edges and vertices. It proves no necessity or uniqueness of
the operator, physical, logical, or empirical interpretation attached to
those labels.

## 4. Owner map and smallest justified implementation

| Exact role | Inspected source / declaration | Consequence for this task |
| --- | --- | --- |
| Arbitrary-ring Peirce blocks and nilpotent corners | `OperatorAlgebra/PeirceSpine/Basic.lean`: `conePlus`, `coneMinus`, `genV`, `genSig`, corner product lemmas | Reuse the established order conventions. |
| Round-trip support and vanishing equivalence | `OperatorAlgebra/PeirceSpine/ReflexiveObserver.lean`: `reflexive_cycle_support_and_reconstruction`, `metric_zero_iff_curvature_zero` | Do not duplicate these as newly discovered structures. |
| Exact compression defect | `Core/PeirceCompressionDefect.lean`: `defect_compression_peirce_transfer`; `OperatorAlgebra/PeirceDefectBridge.lean`: `peirce11_idempotencyDefect_sub` | Cite the correction and preserve its sign. |
| Nonzero partner eigenspaces | `OperatorAlgebra/PartnerEigenspaces.lean`: `unitEigenspaceEquiv`, `nonzeroEigenspaceEquiv` | Spectral correspondence is already present; nonemptiness is the missing, false inference. |
| Nonzero maps with zero overlap | `OperatorAlgebra/PeirceSpine/PeirceOverlapCounterexamples.lean` | Reuse the existing boundary countermodel. |
| Partial-isometry source/range idempotence | `Algebra/NonCommutativeIsometry.lean`: `rangeProjection_idempotent_of_partial_isometry`, `sourceProjection_idempotent_of_partial_isometry` | Add only genuinely useful composition/closure consequences. |
| Matching-support composition | `OperatorAlgebra/RealProjectionMurrayVonNeumann.lean`: `mvn_trans` | Existing support endpoint calculation should be reused or cited. |
| Supported algebraic rotation | `Core/PeirceRotor.lean`: `phaseRotor_formula`, `phaseRotor_mul`, `phaseRotor_inverse`, `phaseRotorUnit` | Reuse the actual dual-seed equations and ambient unit construction. |
| Analytic real rotor derivative | `Canonical/ReflexiveRotorRealTime.lean`: `realRotor`, `hasDerivAt_realRotor`, `realRotor_generator_left`, `realRotor_generator_right` | An actual derivative is present; exponential identification is a separate statement. |
| Genuine noncommutative direct limit | `OperatorAlgebra/PeirceCoupling/CartanDirectLimit.lean`: `of_injective`, `support_of_ne_zero`, `lift_exists_unique` | Use the constructed quotient and its visible injectivity hypotheses. |
| Genuine Drazin construction | `Canonical/Drazin.lean`: `IsDrazinInverse.of_core_nilpotent_split` | Construct the required invariant core, inverse, and nilpotent block before invoking it. |
| Compression and commutation in a C-star carrier | `OperatorAlgebra/ProjectionLocalization.lean`: `compression_idempotent_iff_commute` | Confirms that commutation conditions are substantive, not automatic. |
| Distinct defect iteration behaviors | `OperatorAlgebra/PeirceSpine/ReflexiveObserver.lean`: `observer_matrix_meta_reflection_collapse`, `observer_matrix_metric_tower_ne_zero` | A universal persistence claim is not supported. |
| Native full algebraic spectrum reciprocity | Mathlib `Algebra/Algebra/Spectrum/Basic.lean`: `spectrum.nonzero_mul_comm` | Reuse native spectrum rather than replacing it by eigenvector existence. |
| Nonzero nilpotent round trips | Candidate `PeirceRoundTripCounterexamples.lean` | Add the explicit noncommuting `M₄(ℝ)` countermodel and native spectrum result. |
| Native supported-arrow groupoid | Proposed `Categorical/PartialIsometryGroupoid.lean` | Builds source/target-sensitive composition and adjoint inverses without changing Lean's logic. |

The bounded searches supporting this map used definitions, statement text,
imports, and alternate terminology across `Core`, `Algebra`,
`OperatorAlgebra`, `CliffordWeyl`, and `Canonical`. The table records
positive source findings, not a claim of exhaustive repository-wide absence
of every alternative implementation.

## 5. Valid theorem dependency sequence

The mathematical dependencies have several branches. The following order
does not insert arrows justified only by interpretation:

| Stage | Mathematical construction | Actual prerequisites |
| --- | --- | --- |
| A | Complementary idempotents and grading involution | An associative ring; `p²=p`. |
| B | Four Peirce blocks, corner support, square-zero off-diagonal maps | A. |
| C | Ordered round trips, sum/commutator identity, exact compression defect | B and the associative-ring expansion. |
| D | Partner eigenspace equivalence | Composable linear maps and a nonzero field scalar, or a unit scalar over a commutative ring; independent of partial isometries. |
| E | Nilpotent spectral countermodel | Native algebraic spectrum, nilpotence, and a full matrix realization of B–C. |
| F | Source/range star projections and composable partial isometries | A specified star structure, the partial-isometry equations, and the support compatibility condition. |
| G | Support split and invariance criterion | An idempotent endomorphism; commutation with the independent operator for two-sided invariance. |
| H | Supported rotation | F plus real scalar action and the proved polynomial relations; analyticity/completeness for the exponential statement. |
| I | Survival in a directed limit | A specified directed system, compatible elements/maps, and injectivity or an explicit nonvanishing theorem. |

There is no established dependency from E, F, or H to empirical validity,
from a nonzero defect to I, or from this finite list to a unique physical or
logical synthesis. Those claims require separately stated constructions.

## 6. Acceptance boundary for the implementation

The useful new theorem surface consists of the actual missing boundaries:
partial-isometry composition under visible support hypotheses, explicit
matrix failures of unrestricted closure, and
nonzero nilpotent round trips with spectrum `{0}`. The native supported-arrow
groupoid packages the proved composition law into an actual category. All abstract algebraic
results should retain an arbitrary noncommutative carrier. Concrete
countermodels should retain their full matrix operations and exact dimensions.

Before promotion, the final source must compile under the pinned Lean and
Mathlib versions, contain no proof placeholders or custom axioms, and have
its declaration axiom dependencies checked. The semantic review must ensure
that no theorem assumes the conclusion through a witness structure and
that no title or docstring upgrades a finite identity into a physical,
statistical, cohomological, or categorical classification.

This is the independent mathematical and statement-level review. The exact
compiler, source-gate, and axiom results are recorded separately in
`PEIRCE_ROUNDTRIP_VERIFICATION.json`; they are not inferred from this review.
