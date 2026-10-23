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

The projections onto im(N^m) minus those onto im(N^(m+1)) describe the
decreasing **range filtration**, not exact time to absorption. Exact death
layers use the increasing kernels ker(N^(m+1)) minus ker(N^m). On the ambient
space, the range-shell sum is I when N is nilpotent, not the oblique F.
One must specify the restricted carrier V_N and its induced inner product.

Multiplying a three-sector sum by F gives an algebraic sum E+Fpq+FB+Fnull=1.
It does not automatically give idempotent or orthogonal summands. Commutation
with F suffices for idempotence; self-adjointness of F is additionally needed
for orthogonality. An alternative is to form the MP decomposition intrinsically
on V_N and transport it through the algebraic direct sum, obtaining oblique
ambient projections. Ambient N† cannot silently replace the restricted inverse.

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

Implementation and independent audit/QA results are recorded below after the
locked checks. No full-repository acceptance is inferred from narrow builds.
