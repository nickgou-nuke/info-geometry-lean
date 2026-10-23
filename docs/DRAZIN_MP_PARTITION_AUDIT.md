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
