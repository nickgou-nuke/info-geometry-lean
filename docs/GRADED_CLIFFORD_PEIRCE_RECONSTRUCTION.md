# Graded Clifford–Peirce reconstruction

## Source, repository search, and status

Source: `Pasted markdown(20260906-080642).md` (150 parsed lines). This is a
corrected reconstruction of its six-section argument, not a transcription
endorsing its final universal-algebra claim.

Base: `main` at `b0fa422e6cb6d3da5be7cbbb5ecfae5c12f3237b`. The new branch is
independent of draft PR160 and PR162: none of their definitions is copied or
overwritten. Relevant open-branch sources were inspected for overlap.

The new source contains five theorem owners, an aggregate, and an audit:
65 theorem declarations and 82 total audited declarations. Every theorem has
an explicit proof script. The actual focused build attempt exited 127 before
Lean execution because `lake` is absent. No new source has been elaborated in
this environment. Compilation errors and inherited axiom dependencies may
remain. Independent exact arithmetic passed 2,629 assertions; those tests do
not replace kernel checking.

### Reused and inspected owners

| Existing source | Actual role | Decision |
|---|---|---|
| `Core/PeirceDecomposition.lean` | Associative binary Peirce reconstruction and the complete routing table | Import, do not recreate the binary table |
| `Canonical/CyclotomicProjectorReadout.lean` | General Fourier readout interface; derived spectral synthesis; concrete order-two instance | Construct a new order-four instance of this existing interface |
| `Canonical/MatrixStageTrifactorFourierCyclotomic.lean` | Concrete two-by-two involution and square-minus-one clock projectors | Do not duplicate the clock matrices; prove an arbitrary-module fourth-root constructor |
| `Algebra/CyclotomicOperatorProjectors.lean` | n-potent separation, nilpotent inverses, scalar geometric sums | Retain the distinction between nilpotency and finite order |
| `Canonical/ExteriorSpinorChiralityBridge.lean` | Existing exterior grade involution | Prove the new clock squares to this exact operator |
| `Clifford/KoszulFoundation.lean` | Native scalar/bivector split and recursive volume-square theorem | Reuse the volume theorem for four-frame signature corrections |
| `Canonical/ChiralExterior3HodgeDiracBlocks.lean` | Existing literal exterior carrier and finite odd block decomposition | No second finite Hodge–Dirac model |
| `Topology/DiscreteDiracHodge.lean` (search result) | Discrete complex/adjoint interface | Not promoted to a smooth Dirac–Kähler theorem |
| PR162, `OperatorAlgebra/KleinDiracKahlerOperatorZorn.lean` at `20fbe3294ca216fd41f2b7b20373b1b8ae3b3b66` | Explicit ring datum `d²=delta²=0`; derives `(d-delta)²=-(d delta+delta d)` | No duplicate ring datum |
| Mathlib `ExteriorAlgebra/Basic.lean` at `8f9d9cff6bd728b17a24e163c9402775d9e6a365` | Literal exterior algebra, universal property, generator extensionality | Construct the degree clock on this carrier |

This is a targeted semantic dependency search, not an exhaustive kernel audit
of every repository file. The general Fourier readout is an interface: its
fields alone do not prove the original Fourier-polynomial construction.
The new fourth-root owner discharges those fields from `U^4=1`.

## 1. Dimensional obstruction and Hodge replacement

The Hodge operator, after the appropriate metric/orientation identifications,
has degree `k -> D-k`. Thus `star(u wedge v)` has degree D-2, not degree one
in arbitrary dimension. The new elementary type-degree theorem says that for
D >= 2, `D-2=1` iff D=3. It is not a proof of the full classification of
norm-compatible cross products. In particular the source's exceptional
seven-dimensional case is not recovered by a Hodge map on all bivectors.

The source's displayed Zorn multiplication also contains a mismatched upper
cross term: in the installed convention it is `-v1 cross v2`, not
`-u1 cross v2`. The native Zorn multiplication is left unchanged.

The scalar/bivector decomposition of TWO Clifford vector generators already
exists in `KoszulFoundation`. A wedge is not automatically curvature: a
connection and its curvature operation are additional data.

## 2. The full graded carrier is not the four-grade truncation

The source first retains only grades 0,1,D-1,D, then correctly mentions all
even and all odd grades in its Peirce section. These two descriptions are
not the same in general. In dimension four, grade two has dimension six and
is omitted from the four-grade layout. The product of two independent vector
generators has a nonzero grade-two component, so that layout is not closed.

Hodge duality is neither a replacement for all intermediate grades nor
identical to left or right multiplication by a volume element without a
convention. Its square depends on degree and signature. In even dimensions
it preserves exterior parity: D-k and k have the same parity. The new source
proves this degree arithmetic, not a previously unconstructed metric Hodge
operator.

The exterior algebra is associative under wedge. The Clifford algebra is
associative under its geometric product. The scalar split-octonion Zorn
product is nonassociative. A vector-space correspondence does not identify
these products. The exact regression test retains a native Zorn associator
witness rather than erasing it by matrix reassociation.

## 3. Peirce decomposition: exact corner matrices

For a previously constructed finite family of orthogonal idempotents with
sum one, define B(X)_ij = P_i X P_j. The new generic source proves

    sum_i sum_j B(X)_ij = X,
    B(XY) = B(X) B(Y),
    B is injective and K-linear,
    P_i B(X)_ij P_j = B(X)_ij.

Products with mismatched intermediate sectors are zero; individual
strictly off-diagonal corners square to zero. This does not prove that a
sum of off-diagonal corners is nilpotent.

Crucially, `B(1)=diag(P_i)`, not the identity of the full matrix algebra
`Matrix (Fin n) (Fin n) A`. The image is corner-valued and has its own unit.
The extension therefore builds a native linear embedding with a proved
multiplication law, not an invalid unital algebra homomorphism into the full
ambient matrix ring. A theorem exposes this unit obstruction whenever some
P_i differs from one.

The projectors are algebraically orthogonal. Without a specified adjoint and
unitarity/self-adjointness data, this does not mean orthogonal projection in
a Hilbert space. They are also not generally primitive: in a four-dimensional
spinor representation the positive chirality projector can have rank two.

## 4. Paravectors and Dirac–Kähler

For a native Clifford algebra of Q, the extension proves directly

    (t + iota(v)) (t - iota(v)) = algebraMap(t^2 - Q(v)).

This is valid in arbitrary dimension and does not require a determinant of
a multivector-valued matrix. The source's top-degree expression should use
an explicitly chosen exterior/Hodge pairing, such as `v wedge star(v)` after
metric identification, rather than an undefined dot product producing a
top form. No such new analytic Hodge structure is asserted here.

The operator identities for d, delta, D and their chiral blocks are already
available in the inspected finite/ring owners. They do not by themselves
construct differential forms on a manifold, a codifferential as an adjoint,
operator domains, spinor equivalence, or a Dirac–Kähler field equation.

## 5. Constructed fourth-root Fourier projectors

On ANY complex module E, let U be a native complex-linear endomorphism with
U^4=1, and write lambda_k=i^k. Define the actual polynomial

    P_k = (1/4) [1 + lambda_k^3 U + lambda_k^2 U^2 + lambda_k U^3].

These coefficients equal the fourth-root Fourier coefficients. The new
proof scripts derive, not assume,

    U P_k = lambda_k P_k,
    P_j P_k = delta_jk P_k,
    sum_k P_k = 1,
    U = sum_k lambda_k P_k.

They also prove that P_k fixes x iff Ux=lambda_k x. This permits missing
spectral sectors and requires no finite-dimensionality or analytic spectral
theorem. The resulting data populate the EXISTING FourierCyclotomicReadout.

If U^2=-1, the same polynomials give

    P_0=P_2=0,
    P_1=(1-iU)/2,
    P_3=(1+iU)/2.

Consequently such an operator cannot supply four nonzero degree-mod-four
sectors merely because its fourth power is identity.

### Signature correction using the existing volume owner

For an orthogonal four-frame the native recursive Koszul theorem gives

    (e0 e1 e2 e3)^2 = Q(e0)Q(e1)Q(e2)Q(e3).

The six interchanges contribute a positive sign. Thus normalized (4,0)
and (2,2) frames give +1, while (1,3) gives -1. This directly corrects the
source examples; no convention switching is hidden in the proof.

### The genuine degree clock

Scale each generator of the native complex exterior algebra by i. Its
square-zero relation allows Mathlib's exterior universal property to extend
this to an algebra homomorphism C. Generator extensionality proves its
composition law and C^4=1. For every ordered wedge word of length k,

    C(v1 wedge ... wedge vk)=i^k (v1 wedge ... wedge vk).

Applying the constructed Fourier polynomials gives exact degree-residue
selection on those words. The new compatibility theorem identifies C^2 with the already installed
exterior grade involution. The clock fixes scalar one, so C^2 is NOT minus
the identity. Multiplying Clifford vectors by i instead changes their square
by a sign; the exterior construction is not silently reused as an automorphism
of a nonzero-metric Clifford algebra.

The extension proves the word-level selection theorem in the native algebra.
A fully bundled graded direct-sum/eigenspace equivalence for all exterior
powers is not asserted as an additional declaration here.

### Ladder covariance is not nilpotency

On the native module C^4, the cyclic shift e_k -> e_(k+1 mod 4) satisfies

    N P_k = P_(k+1) N,    N^4=1 !=0.

The truncated shift e0->e1->e2->e3->0 satisfies the same covariance but has
T^4=0 and T^3!=0. Both use the constructed Fourier projectors of the same
coordinate clock. This proves the source's covariance law needs a separate
truncation or nilpotency theorem.

## 6. Correct hierarchy and next boundaries

The retained hierarchy is

    actual Clifford/exterior carrier and its specified product
      -> constructed finite-order endomorphism
      -> derived Fourier projectors
      -> corner-valued Peirce matrix representation.

The explicit new Fourier constructor is order four. The arbitrary-n Peirce
result accepts an already established Fourier readout; it does not conceal
an unproved arbitrary-n Fourier-polynomial theorem in its hypotheses.
A natural next algebraic extension is that construction for all n>0 over a
splitting field, with primitive-root and invertible-n requirements discharged.
The word-level degree clock can separately be joined to the native graded
exterior-power direct sum. Neither requires redefining Zorn multiplication.

Before any claim of machine certification, run the focused build and all
transitive axiom queries in the pinned repository environment:

    bash scripts/check_graded_clifford.sh
    python3 scripts/audit_graded_clifford_sources.py
    python3 scripts/check_graded_clifford_exact.py

The checker refuses missing axiom reports and permits only propext,
Classical.choice, and Quot.sound. Its local failure is preserved in the
artifact rather than described as a successful verification.
