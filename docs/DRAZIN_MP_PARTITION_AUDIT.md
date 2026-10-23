# Drazin and Moore–Penrose partitions: corrected contract

Provenance: user intake in the 2026-10-23 conversation, headed
“regular core and transient/nilpotent complement”, with proposed module
`DrazinMoorePenrosePartitionAudit.lean`. The intake claimed clean compilation;
that claim is not evidence of a kernel check. This record follows
`skills/epistemic-compilation/SKILL.md` and `docs/ALCHEMICAL_QMS_SOP.md`.

## Mathematical rewrite

For a Drazin witness D for A, set E = AD and F = 1 − E. These are
complementary algebraic idempotents, generally oblique. The existing canonical
owner defines C = A²D and N = A − C = AF, proves A = C + N and CN = NC = 0.
The regular restriction is invertible; this does **not** imply volume
preservation (its determinant need not have absolute value one).
For positive witness exponent k, N^k = 0. For k = 0, F = N = 0 but
the ambient equality N^0 = 0 is false in a nontrivial ring.
The witness predicate does not assert that k is minimal.
The determinant of a nilpotent restriction is zero only when its carrier has
positive dimension; the determinant on the zero-dimensional space is one.

Replacing N by F gives C + F, with two-sided inverse D + F, at every index.
This is an algebraic regularization, with no volume-preservation assertion.
For a finite stochastic P, the zero eigenvalue of I − P is semisimple:
the nilpotent part of I − P is zero. Decaying modes of P generally belong to
the regular sector of I − P. A rank-one stationary projector requires a
one-dimensional fixed space; it is not automatic for reducible chains.

For a Moore–Penrose pair X,M, let p = XM and q = MX. Both are orthogonal
projections. The identity

    pq + p(1−q) + (1−p)q + (1−p)(1−q) = 1

is universal even without the Penrose equations. Its summands become
orthogonal projections when pq = qp. Under that hypothesis the boundary is
B = (p−q)^2 = p(1−q) + (1−p)q, the interior is pq, and
p+q = 2pq+B. Their common null sector is (1−p)(1−q).
The commutator XM−MX is self-adjoint, despite being antisymmetric in its
two arguments. Its zero trace is an algebraic trace identity, not a proved
Stokes theorem for a chain complex.

Nilpotency alone does not imply pq = qp. Orthogonal Jordan shift blocks
satisfy it; arbitrary similarities do not preserve the Moore–Penrose inverse.
The backward-shift interpretation requires an orthonormal (possibly weighted)
shift model. General directed acyclic matrices need not have this geometry.

The square-zero case is stronger: X²=0 forces qp=M X² M=0, and taking
adjoints gives pq=0. The general owner
`Singular/SquareZeroMoorePenrose` derives this from the native Penrose
predicate, also deriving M²=0. Then H=1−XM−MX is a star projection and
H x=x iff Xx=Mx=0 for the left regular module. Its chirality formula is
(XM−MX)²=XM+MX=1−H, not automatically the identity. This includes a
harmonic complement rather than imposing the full CAR relation.

The normalized algebraic operator J=X+M satisfies J²=XM+MX and J³=J,
so it is its own Drazin inverse with witness exponent one. It must not be
renamed the metric Hodge–Dirac operator X+X*: the latter requires the
actual adjoint, whereas M=X* is an additional normalization condition.
For metric Hodge/Green and harmonic-kernel statements use
`Dynamics/ChiralHodgeMoorePenroseBridge`; the algebraic generalized Green
construction remains in `Canonical/HodgeGreenProjectorConstruction`.
`Singular/MoorePenroseChiralDefects` also proves pq=0 iff X²=0, without
assuming that the supports commute, and the four signed chirality actions.
The normalized Jordan self-associator is −X/2, not −2X. Thus a nonzero
associator can occur even for square-zero X; it does not by itself detect
failure of square-zero. Targeted builds and independent QA of the integrated
additions passed with the limited scope recorded below.

Witt isotropy also requires its own carrier and neutral bilinear form:
`Canonical/ParaComplexNeutralForm` derives isotropic Peirce eigenspaces
from anti-compatibility. This is not implied by singular determinant,
nilpotency, or a kernel equation alone. A nonzero idempotent cannot also be
nilpotent. The existing general Peirce multiplication rules, rather than a
new matrix fixture, supply the off-diagonal square-zero-arrow interpretation.

The projections onto im(N^m) minus those onto im(N^(m+1)) describe the
decreasing **range filtration**. They also give exact death time m+1 for
nonzero **row states supported in Q_m, under right action**: Q_m N^(m+1)=0 and
(Q_m N^m) M_m=Q_m. The earlier unqualified rejection of this interpretation
was too strong. For column action use the dual co-range shells
M_m N^m − M_(m+1) N^(m+1), equivalently the orthogonal differences of
ker(N^(m+1)) and ker(N^m). Each power has its own MP inverse; no reverse-order
law is used. The ambient range-shell sum is I, not the generally oblique F.

Under pq=qp, multiplying the three-sector sum by F gives E+Fpq+FB+Fnull=1.
Without that hypothesis the right side is 1+F[p,q].
It does not automatically give idempotent or orthogonal summands. Commutation
with F suffices for idempotence; self-adjointness of F is additionally needed
for orthogonality. An alternative is to form the MP decomposition intrinsically
on V_N and transport it through the algebraic direct sum, obtaining oblique
ambient projections. Ambient N† cannot silently replace the restricted inverse.

The power-shell family has extra structure absent from arbitrary MP sectors:
F P_m=P_m for m>0. Consequently the dressed ranges F P_m F are nested
algebraic idempotents even when F is oblique. Their differences
S_m=F Q_m F=Q_m F sum to F and annihilate one another and E on both sides.
Here “orthogonal” means zero products, not self-adjointness. For row action,
S_m A^(m+1)=0 with recovery at m. For a state with a regular component,
“entry into the core” means extinction of its transient component; the two
invariant subspaces do not transfer nonzero states between one another.
Individual shells can be zero. The core is invariant, not pointwise fixed.
The native owner `Canonical/DrazinNilpotentShellResolution` proves these claims,
including the recovery formula (S_m A^m) M_m F=S_m.

### Inter-shell corners: corrected intake contract

The subsequent `InterShellChiralHodgeAudit` / `NoncommutativeShellFiltrationAlgebra`
intake is conditional algebra, not evidence of compilation. In particular,
the supplied generic snippet contains a `sorry` and an inconsistent real-valued
MP family; adding a differently named corrected theorem does not remove that
earlier declaration. No duplicate inverse predicates or monolithic packet are
imported from the intake. Over an arbitrary coefficient ring, MP families and
the individual corner inverses are hypotheses, not automatic existence claims.

`Canonical/DrazinShellCascade` supplies the generic star-ring identities
S_m A S_r=0 for m≤r and
A=E_C A E_C+Σ_(m<k) S_m A (Σ_(r<m) S_r).
Distributing the inner finite sum gives the proposed double-sum reconstruction.
For m≠r, (S_m A S_r)²=0 follows from S_r S_m=0 and associativity;
the existing square-zero MP theory therefore applies to each such corner.
Different corners can compose nontrivially: local square-zero does not force
the sum of the corners to have square zero. This intake check does not add a
new theorem asserting a nonzero or faithful adjacent-shell transition.

The idempotents E_C,E_N commute with A, not generally with the entire ambient
algebra. E_N R_m E_N is a corner compression, not conjugation by an invertible
map. The equality E_N N^m=N^m requires m>0; at m=0 its left side is E_N.
For row action a corner S_m A S_r goes from m to r; for column action it goes
from r to m. Source/sink terminology must specify which convention is used.

With d=S_m A S_r and B its MP inverse, S_m(dB)=dB and (Bd)S_r=Bd
are valid one-sided absorption laws. Oblique S_m,S_r do not justify reversing
these products or placing B in the opposite oblique corner. For real matrices
the latter absorption localizes the column range of Bd to im(S_rᵀ), not
automatically im(S_r). The local harmonic projector 1−dB−Bd acts on the
whole ambient space; it is not a projection solely within the two named
shells. The same Witt, metric-adjoint, and supported-grading limitations
established above remain in force.

## Anomalies, triple products, and graph carriers

The symmetric associative triple T(X,Y,Z)=XYZ+ZYX has diagonal
T(X,Y,X)=2XYX. The latest intake's proposed identity
T(X,Y,Z)=(XY)∘Z−[X,ZY], for the unnormalized Jordan product, is false:
its right side minus its left side is [Z,X]Y. The unconditional correction
is T(X,Y,Z)=(XY)∘Z−Z[X,Y]. With the repository's half-normalized Jordan
product, replace the first term by 2((XY)∘Z).

The sandwich defect A−AYA is an inner-inverse defect, not the standard
Kantor operator K(X,Y)Z=T(X,Z,Y)−T(Y,Z,X). For the symmetric associative
triple that Kantor operator vanishes by outer symmetry. In
`Singular/DrazinReflexiveDefect`, Drazin commutation identifies A−ADA
with the existing nilpotent part. Its vanishing is equivalent to the same
candidate D satisfying the index-one equations; this does not assert that
the supplied exponent k was minimal. The division-free triple balance is
T(A,D,A)+2N=2A. These distinctions preserve, rather than rename, the
repository's separate Kantor and Cantor constructions.

For arbitrary MP supports, define Δ=p+q and Γ=p−q. The universal overlap is
Δ−Γ²=pq+qp. Ordered overlap vanishes iff A²=0 in a star ring. Equating
vanishing symmetric overlap with square-zero additionally requires care
about 2-torsion: over characteristic two, A=M=1 refutes that equivalence.
No arbitrary-ring version of that stronger equivalence is asserted here.
Likewise the dependency diagram is not a formal strict causal poset without
a specified carrier, relation, and order laws.

### Subsequent star-ring “loop closure” intake

The proposed local conclusion is valid conditional algebra: if e₂e₁=0,
d=e₁Xe₂, and B is an MP inverse of d, then d²=B²=0. Writing p=dB,
q=Bd, the existing square-zero owner gives pq=qp=0. Hence both the
symmetric overlap pq+qp and [p,q] vanish; the Jordan associator
assoc(p,Z,q) vanishes for every Z. This is distinct from assoc(d,d,B),
which need not vanish. The latter equals −2d for the unnormalized product
and −d/2 for the repository's normalized product.

The global assertion that N²≠0 forces both obstructions to be nonzero is
false. For the real shift J₃, the existing `MoorePenroseSectorExamples`
owner proves the supports p=diag(1,1,0) and q=diag(0,1,1). Thus
pq+qp=diag(0,2,0)≠0 while [p,q]=0 and assoc(p,Z,q)=0 for every Z,
despite J₃²≠0. In characteristic two the same shift and transpose satisfy
the Penrose equations but even pq+qp=0. Thus the symmetric-overlap
nonvanishing assertion cannot be lifted to arbitrary star rings unchanged.

The supplied `NoncommutativeStarRingPeirceKantor` module and LaTeX table also
repeat the false triple identity corrected above and call d+B self-adjoint
without an additional hypothesis. Their blanket verification claim is rejected.
The maintained square-zero, Drazin-residue, and shell-cascade owners already
use generic rings/star rings; introducing duplicate inverse predicates does
not generalize them. MP and Drazin inverse existence remains conditional,
including on operator-algebra carriers. A cycle in a conceptual workflow is
not a cycle in a strict partial order or a theorem-dependency DAG.

The inverse-kernel owner distinguishes S=AD, R=AM, and T=MA. Its left chiral
anomaly is [S,T], its right anomaly [S,R], and the Einstein anomaly [R,S].
Thus Einstein is minus the **right**, not generally the left, anomaly.
These are support-projector commutators, not automatically the raw [D,M].
The new bridge retains the exact sector defect 1+[S,T] and the corresponding
Einstein sign. With the owner's normalized Jordan product,
assoc(S,Y,T)=(1/4)[Y,[S,T]]. Ordinary operator multiplication stays associative.

`Canonical/JordanWignerCantorRepresentation` owns the global real Cantor
algebra equivalence and its triple/superbracket transport.
`Clifford/ParaKahler55PositiveGrassmannianCantorBridge` owns cylinder triple
concatenation and graded triple identities. These must not be replaced by a
claim that ordinary matrix multiplication is nonassociative. The projected
associator in `Canonical/ProjectedNonassociativeBianchi` instead measures
readout/inclusion leakage. An algebra equivalence alone does not establish
star preservation and therefore cannot silently transport MP inverses.

`Canonical/CuntzInverseSectorPartition` uses the actual two-isometry carrier:
q+ q− and q− q+ are disjoint excitation supports. The boundary square is
their sum; its complement is the Toeplitz vacuum defect. This defect may be
zero even without assuming completeness; no nonzero vacuum is claimed.
Chiral parity can be nonzero while the MP/Drazin anomaly is zero.
The triple commutator obeys the derivation rule on these actual arrows.

`Streaming/GraphDifferentialPenrose` uses the vertex/edge cochain carrier of
`BipartiteGraphDirac`, not scalar proxies. The graph differential is square
zero and has zero Drazin inverse. Its codifferential is an adjoint, not in
general a pseudoinverse: the first Penrose identity holds exactly when
B Bᵀ B=B. This normalization condition is retained explicitly.

Nonzero constant scalar rescaling preserves the support products and scales
inverse witnesses inversely. This is global scalar homogeneity; no local Weyl
geometry is asserted. DMP products are algebraic compositions of the existing
inverses, not a reconstruction of missing nilpotent dynamics.

## Owner grounding and theorem contract

Risk R2; ring and star-ring algebra, with finite real matrix examples.
No new inverse predicate or carrier is needed.

- `Canonical.Drazin.IsDrazinInverse`: `a*b=b*a`, `b*a*b=b`,
  `a^(k+1)*b=a^k`; owns `projection`, `complementaryProjection`, `core`,
  `nilpotent`, complementary idempotence and both cross-product vanishings.
- `Canonical.DrazinCoreFlow`: positive-power nilpotency and
  `complementaryProjection_range_eq_drazinCore`; the latter legacy name
  denotes the generalized kernel, not the invertible core.
- `Singular.MoorePenrose.IsMoorePenroseInverse`: four Penrose equations;
  owns range-projector idempotence, self-adjointness and inverse uniqueness.
- `QuantumContext.MarkovAttentionGroupInverse`: finite stochastic Laplacian
  group-inverse existence and regularized inverse, with native range/kernel
  statements. These existing results are reused by reference, not duplicated.
- Mathlib `IsStarProjection.mul`, `.one_sub`, `.add` supply projection calculus.

New proof targets: arbitrary-index regularization over a ring; commuting
MP support-sector identities and star-projection laws; the exact commutation
obstruction without that assumption; compatible refinement by a third
projection; nonzero scalar transport; full matrix shift witness and a
nilpotent countermodel to unconditional boundary idempotence.

Causal order: inverse equations → support idempotence → commutation-conditional
sector projections → compatible refinement. Drazin equations separately give
regularization. Matrix examples instantiate these theorems, without promoting
their geometry to arbitrary nilpotents.

Adjacent claims excluded from new theorem scope: determinant and volume
theorems, classification of all nilpotent chains, shell subspace theorems,
continuum/colimit or gauge geometry, and a stochastic convergence theorem.
The prose above states the necessary corrections; it is not a claim that all
these adjacent statements have been newly formalized.

## Verification record

### Split-Clifford / Cayley intake corrections (2026-10-23)

The user's revised polynomial products have the correct normalization:
with `Q1=d+B`, `Q2=d-B`, `Gamma=dB-Bd`, one has
`Q2*Q1=Gamma` and `Q1*Q2=-Gamma`, not twice these values.
These identities do not identify MP inversion with adjunction: for example,
over real matrices `d=2 E12` has MP inverse `B=(1/2) E21`, not `star d`.
The support projections and Gamma are self-adjoint by the MP laws; the
claimed adjoint properties of Q1 and Q2 require the separate partial-isometry
condition `B=star d`.

The factors `Cplus=1+Q2` and `Cminus=1-Q2` obey
`Cminus*Cplus=Cplus*Cminus=1+Delta`. Thus the displayed products with
opposite factors are sandwiches, not conjugations by inverse elements.
In a unital real algebra the genuine inverse and Cayley transform are

```
(1-Q2)^(-1) = h + (1/2) (Delta+Q2)
U = (1+Q2)(1-Q2)^(-1) = h+Q2
U^(-1) = h-Q2,   U^2 = h-Delta,   U^4 = 1.
```

Here `h=1-Delta`. The order divides four, not necessarily exactly four.
Unitarity of U requires `B=star d`. A general star ring does not supply the
required division by two. Nor does `Y^3=Y` ensure that `1-Y` is invertible:
`Y=1` already refutes that assertion in a nonzero ring. Extending Q1 or
Gamma by h is therefore not automatically their Cayley transform.
The real Clifford-algebra identification needs a real algebra carrier and
faithful nonzero active representation, not merely `[Ring A] [StarRing A]`.
These are algebraic intake corrections, not certification of either pasted
Lean packet; no duplicate inverse or master-bundle module is introduced.

### CAR to finite-chain intake contract (2026-10-23)

The user identifies SuperchargeCARCCRBridge, MajoranaPfaffianNaturalClosure,
KitaevChainMajoranaZeroModes, ProjectivePfaffianDeterminantCounts, and
KreinMajoranaZeroModeBlock as ingredients for an end-to-end bridge.
Source inspection distinguishes the concrete real doubled CAR carrier, the
complex 2-by-2 Majorana pair, and the arbitrary-ring chain family. These are
not identified by naming. The chain owner defines the entire finite sum but
its existing boundary lemma only treats one bilinear bond. The first narrow
implementation target is commutation of the left endpoint with that defined
sum, assuming `IsMajoranaBasis`, positive length, and commutation of the
coefficient with the endpoint. This is an operator commutator zero mode,
not a vector in the kernel of the many-body Hamiltonian.

The cited PfaffianKernel contains `pf_sq_eq_det` as input data, and the
Krein bridge takes an arbitrary `toMatrix` plus an explicit model equality.
Neither supplies the missing concrete chain coefficient matrix map. A
nonzero kernel vector and a derived Pfaffian criterion for that same matrix
remain separate obligations; no bundled end-to-end theorem is claimed here.

The finite-sum lemma `left_boundary_commutes_sweetSpotHamiltonian` is now
independently accepted with this limited scope. After making the endpoint
index contradictions explicitly Nat-valued, the locked target build passed
(4083 jobs), as did the direct Lean and axiom checks. Its dependencies are
only `propext`, `Classical.choice`, and `Quot.sound`. Source SHA-256 stayed
`5b20fc2d2178e56f954d277c13d0d4d26371d0cfbf0da1bc30654256e8ed6f46`;
the staged source matched the worktree. Whitespace passed, with three
advisory scanner warnings and no blocking findings. Independent A-A accepted
the source and the explicit-index repair. No full bridge certification follows.

### Undoubled superderivation implementation contract (2026-10-23)

Target owner: `Canonical.ChiralSuperderivationColimit`; existing imports and
Boolean parity convention are retained. For any associative ring, charge `Q`,
element `X`, and Boolean parity `p`, prove that applying `oddSuperDerivation`
twice with the second parity `!p` equals `innerDerivation (Q*Q) X`.
Then characterize its vanishing exactly by `Commute (Q*Q) X`.
This closes the undoubled-composition gap in this owner without dividing by
two, adding an inverse predicate, or imposing scalar/characteristic assumptions.
The existing doubled anticommutator theorem remains unchanged. The new
statements do not construct a graded carrier, prove global centrality, or
classify a generated algebra. Independent A-A accepted both declarations.
Independent QA passed the locked target build (8927 jobs), direct Lean check,
static/proxy/whitespace checks, and explicit axiom inspection: both new
declarations use only `propext`. Owner hash was stable at
`5c13ec15b6735afc8203c3bc9078a36fdbda81d1e54bb965b164642b689c239b`.
One pre-existing transport-identity vacuity advisory remains; this is bounded
acceptance of the two new declarations, not a clean full-repository release.

### Superalgebra intake: corrected carrier and parity contract (2026-10-23)

Provenance: the user-supplied `NoncommutativeDiracSuperalgebra` packet claims
that its five Peirce corners decompose the full matrix algebra and that its
odd superderivation is globally square-zero. Independent researcher,
refuter, and A-A review reject those scope claims (`countermodel_found`).
The pasted module is not certified by the checks below.

For a square-zero MP pair write `p=dB`, `q=Bd`, `h=1-p-q`,
`Delta=p+q`, and `Q=d+B`. The five supplied corners span the centralizer
of `Delta`, namely `Delta A Delta + h A h`, not all of `A`. The omitted
corners are `p A h`, `h A p`, `q A h`, and `h A q`.
The correct full Peirce grading uses `e=p+h=1-q`:

- even: `e A e + q A q`;
- odd: `e A q + q A e`.

These are direct additive corner decompositions over any ring. The
self-adjoint involution `J=e-q` implements the automorphism `X -> J X J`;
`J` itself is an element, not an automorphism. Identifying these corner
spaces with the complete sign eigenspaces requires cancellation of additive
2-torsion (invertibility of 2 suffices). In characteristic two `J=1`, so
sign tests cannot recover the still-valid corner grading. The supported
tripotent `Gamma=p-q` is not a replacement: `h A h` both commutes and
anticommutes with it.

On homogeneous inputs the odd superderivation is a commutator on even
elements and an anticommutator on odd elements, with parity flipped after
each application. Its undoubled square is `[Q^2,X]=[Delta,X]`, not zero
on the whole ambient algebra. Equivalently, with `alpha(X)=J X J`, use
`delta(X)=Q X-alpha(X) Q`. Square-zero holds on the centralizer of
`Delta`. Applying the anticommutator twice without the parity change is
a different operation.

An exact refutation is `d=E12`, `B=E21` in real 3-by-3 matrices, with
`h=E33` and `X=E13`. Both supplied five-corner projection parts of `X`
vanish, yet `X` is nonzero and is even for `J=diag(1,-1,1)`.
Moreover `[Delta,X]=X`, and the correct superderivation sends
`E13 -> E23 -> E13`. Thus centrality and square-zero fail globally.

For a commutative scalar ring `R` and a unital associative `R`-algebra `A`,
the scalar-generated algebra receives the natural surjection
`Mat_2(R) x R -> R<d,B>`, sending coefficients to `p,d,B,q,h`.
An isomorphism requires faithful scalar action on the active and harmonic
factors, respectively (injectivity of `r -> r p` and `r -> r h`). Over a
field, nonzero `d` and nonzero `h` suffice; zero supports remove factors.
The full active corner is a different object, with coefficient corner
`p A p`, not automatically the scalar ring. Ordinary generated-algebra
claims must also be distinguished from star-closure: `B` need not be
`star d`, and `Q` need not be self-adjoint.

Reuse is through `Algebra.PeirceDeWittChiralSplit` (parameter `e=1-q`),
`Core.PeirceDecomposition`, and
`Canonical.ChiralSuperderivationColimit`. No duplicate inverse predicates,
bundled master module, or toy replacement was introduced. The latter
owner's `oddSuperSquare_eq_innerDerivation` is specifically a **doubled**
superderivation anticommutator, giving `[Q*Q+Q*Q,X]`; it is not an
undoubled-square theorem or a construction of a graded carrier.

Independent QA returned `accepted_limited_scope`: shared-locked builds of
PeirceDeWittChiralSplit and ChiralSuperderivationColimit passed (8929 jobs),
as did sequential locked direct checks. Axiom inspection of
`peirce_even_odd_decomposition`, `grading_sq`,
`grading_conjugates_oddPart`,
`oddSuperAnticommutator_eq_innerDerivation`, and
`oddSuperSquare_eq_innerDerivation` reported only `propext`.
Scoped whitespace checks passed and both source hashes stayed stable:
`aa86e5e1f53423d8bfbb90dadba2c1a38fad4c82fc433db92b9743aa2cbf470a`
and `d471f8f1a15ea61ff0deeb3b228e63579cc05f41f81cd9d2adf7c4131095f8f9`.
Dependency dirty-tree notices remain. This does not certify the submitted
code, the unconditional matrix-algebra classification, or a global
square-zero differential.

### Inter-shell intake review (2026-10-23)

No duplicate Lean implementation was added. Independent A-A accepted the
corrected inter-shell contract. Independent QA-A returned
**ACCEPTED_WITH_LIMITED_SCOPE** for the existing owner proofs:
locked `Canonical.DrazinShellCascade` build passed (3182 jobs); sequential
locked direct checks of Cascade, Core PeirceDecomposition, SquareZeroMoorePenrose,
and MoorePenroseChiralDefects all passed. The triangular-vanishing and
core-plus-cascade reconstruction theorems use only `propext`, `Classical.choice`,
and `Quot.sound`. All four source hashes remained stable; Cascade SHA-256 was
`9b66395ee426cb9d41b97a45affbc6c9060ebf57bec79e9f92bd6b42ee5ff16b`.
Placeholder and scoped whitespace checks passed. Three unused-StarRing
warnings in Cascade remain; a static unused-hypothesis flag is discharged
semantically because `omega` consumes `hmr`, and two vacuity advisories concern
genuine annihilation identities. This is not certification of the pasted code
or of nonzero shells, minimal index, Witt geometry, or metric self-adjointness.

### Square-zero, chiral, and reflexive-defect extension (2026-10-23)

Independent A-A Darwin accepted the corrected owner scope and the revised
square-zero/anomaly/triple documentation. Independent QA-A Singer returned
**ACCEPTED_WITH_LIMITED_SCOPE** for the current integrated sources:

- Shared-locked `Singular.All` and the three extension Audits: PASS,
  3335 jobs, exit zero.
- Six sequential direct Lean checks under `BuildLock` (three owners and
  their three Audits): PASS.
- All 27 audited declarations use only subsets of `propext`,
  `Classical.choice`, and `Quot.sound`; `residue_eq_nilpotent` uses none.
- Additional locked axiom check of
  `Core.JordanAssociator.kantorTriple_eq_jordan_commutator`: PASS, standard
  foundational axioms only.
- OpenGauss and stripped-source placeholder checks: zero findings across
  eight scoped files. Scoped whitespace check: PASS. Semantic-vacuity check:
  zero errors; the one `harmonic_mul_eq_zero` advisory was independently
  adjudicated as genuine conditional annihilation, not vacuity.
- Source hashes stayed stable during checking despite an unrelated HEAD
  advance. Owner SHA-256 prefixes: SquareZero `f00a4254e0928c0d`,
  ChiralDefects `7c9b66cda476a042`, ReflexiveDefect `00675d5473480bfe`;
  Core JordanAssociator `af8e5883cd2ab912`.

Existing dependency warnings and Core unused-simp warnings remain. This
acceptance does not cover the entire pasted packet, a minimal Drazin index,
physical identifications, or stability of the global worktree. Earlier QA
rejection during concurrent source editing was superseded only after the
repaired snapshot passed these independent checks.

### Idempotent tangent intake: theorem contract

The 2026-10-23 supercolor intake conflates two different corner geometries.
For `d_i` in `p A s_i` and `B_i` in `s_i A p`, orthogonal source
idempotents annihilate `d_i B_j`, not `B_i d_j`. A shared normalized target
can produce matrix units `B_i d_j`; fully disjoint pairs instead have sector
supports central in their generated algebra (not necessarily the ambient ring)
and no off-diagonal color products. Neither counting charges
nor a conjunction of identities establishes a Lie-superalgebra isomorphism.

The first source delta is `Core/PeirceTangent.lean`: over an arbitrary
associative ring, for `p*p=p`, prove `p*x+x*p=x` equivalent to vanishing
diagonal Peirce corners, and recover its off-diagonal expansion. Derive the
reflection anticommutator with its explicit factor of two. Connect the
equation to `Singular.MoorePenrose.exactSupport` using the existing
`Core.DiracSuperalgebra.partial_matrix_unit_identities`, whose hypotheses
are `IsMoorePenroseInverse a m` and `a*a=0`. Do not duplicate the MP predicate.
No manifold, self-adjoint tangent-space identification, characteristic-free
reflection converse, SUSY classification, or shared-target centrality is
claimed. The source-confirmed existing Grassmannian owner
`Canonical/SuperGrassmannianManifold` defines algebraic linear idempotents;
its name is not evidence for those stronger claims. The finite contracts are
kernel-checked in `Core.PeirceTangent` and `Core.SuperGrassmannianSusy`.

Independent QA Singer accepted `Core.PeirceTangent` with limited scope:
locked target build passed (3189 jobs), direct Lean check passed, and all
five declaration axiom checks used only `propext` / `Quot.sound`.
The checked source SHA-256 was
`c4ed8bfb44ccf77fef2bdf1073fc89d86b2a3ab86e7847fe1874c5fccbe853a5`.
Independent A-A Sagan found no mathematical error in those five statements.
The off-diagonal expansion theorem is forward-only; its converse and a
self-adjoint tangent theorem are not claimed by this module.

### Finite Majorana coefficient-action contract (in progress)

The requested chain/Pfaffian bridge must use the same coefficient matrix,
not a conjunction of unrelated bulk and boundary results. The inspected
`Canonical.MajoranaChiralPfaffianBridge.car_majorana_chain_pfaffian_bridge`
explicitly keeps those components separate. The next owner extension uses
`Canonical.KitaevChainMajoranaZeroModes.IsMajoranaBasis N gamma`, namely
`gamma i * gamma j + gamma j * gamma i = if i = j then 2 else 0`.
The carrier is a nontrivial associative real algebra. The coefficient map
is Mathlib's existing `Fintype.linearCombination ℝ gamma`, not a new
Majorana-field structure. Anticommuting with `gamma k` must recover
`(2 * v k) • 1`, proving this map injective. For a real skew matrix K,
the quadratic element `(1/4) • sum i,j, K i j • (gamma i * gamma j)`
must act on that map by the ordinary commutator as `K.mulVec`.
This establishes the finite operator/coefficient-kernel identification;
specializing the actual chain matrix and transporting its signed Pfaffian
criterion remain separate obligations. No bulk-phase/boundary equivalence,
many-body Hamiltonian kernel, or continuum result is asserted. The summed
quadratic-action theorem is still open; the current source only supplies
coefficient recovery, injectivity, the monomial commutator, and the definition.

### Concrete color multiplication and adjoint tests

The user requested non-vacuous finite examples and a truthful Core closure
API. `Core.SupercolorMatrixExamples` uses real matrix units on `Option ι`:
`d_i = e_(some i),none` and `b_i = e_none,(some i)`. Thus `Fin 2` is a
three-dimensional matrix carrier and `Fin 4` a five-dimensional carrier.
The common co-range is `e_none,none`, and every color product is the nonzero
matrix unit `e_(some i),(some j)`. These are not disjoint-support systems.

`Core.SupercolorMultiplication.colorBoson_mul_of_common_source` proves
`E_ij E_lm = if j=l then E_im else 0` under the explicit common-co-range
hypothesis `∀ i, b_i d_i=q`; the companion commutator theorem proves the
corresponding two-term closure formula. The base MP absorption laws alone
do not imply the matching-middle formula. Adjoint statements require the
explicit `b_i = star d_i` hypothesis. No `sl(k|1)` representation,
super-Jacobi closure, or physical extended-SUSY classification is claimed.
The examples exercise matching and mismatched products, nonvanishing, and
star symmetry; `tests/InfoGeometryTests.lean` contains declaration checks.

### Earlier inverse-sector audit

The implementation is collected by `Canonical/InverseSectorAudit.lean`.
It includes `Canonical/DrazinNilpotentShellResolution` for the oblique resolution,
`Singular/NilpotentShellAbsorption` for both action conventions, native
inverse-kernel/Cuntz/graph bridges, and finite matrix counterexamples.
The finite examples use direct exact Lean arithmetic; no numerical CAS
result is substituted for a proof.

On 2026-10-23 the parent ran locked targeted builds of these modules and the
aggregate audit. Independent A-A Darwin then returned code PASS and, after
the recorded scope corrections, documentation PASS. Independent QA-A Singer
returned **ACCEPTED_WITH_LIMITED_SCOPE**, reporting:

- `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock
  InfoGeometry.Canonical.InverseSectorAudit`: PASS (3296 jobs).
- Fourteen sequential scoped `lake env lean` checks under the shared lock:
  PASS; source hashes unchanged during verification.
- Fifty-nine printed axiom reports: only subsets of `propext`,
  `Classical.choice`, and `Quot.sound`.
- Scoped header, placeholder/unsafe, no-hypothesis, and whitespace checks:
  PASS. The semantic-vacuity gate passed with two reviewed advisory warnings.
- OpenGauss screening: thirteen of fourteen files clean. The finite examples
  still trigger T16 witness recognition despite the kernel-checked
  `chain3_inverse_noncommuting` and `skewChain_inverse_noncommuting` theorems.
  The checker was not bypassed or modified.

Residual verification scope: that static-recognition discrepancy and the
parent's unfinished full-stage gate. Other sessions are editing unrelated
owners and the shared index; no full-repository or stable-global-index
acceptance is claimed. Existing dependency warnings are not attributed to
these new theorem proofs. No cache cleaning or dependency update was used.
