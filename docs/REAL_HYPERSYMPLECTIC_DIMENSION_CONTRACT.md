# Real hypersymplectic leaf dimension: theorem contract

## Source and intent

Source: `docs/intake/2026-11-17-real-hypersymplectic-dimension.txt`, the exact
user attachment `Pasted text(20261117-125328).txt`.
SHA256: `bf9f75a5f439dfc01b3b39510e58facd4f3ea22ae7462e63f63f6046849e181c`.

The request continues the real Hestenes/Krein operator and uncertainty work.
This extension reuses the existing real split-quaternion and Peirce owners.
It closes the generic finite-dimensional leaf parity gap explicitly recorded
in PR386; it does not replace the existing positive Hilbert uncertainty API.

Base: PR386 `1838b7dfc27cac18937136f6e4c168a8dc314e29`, based on main
`08c34e03f610b452e03422037949196dc7d92d6d`. The initial contract used
`bf4d94533f76834e325b5c36725fb76f00481260`; the upstream proof repairs were
incorporated before publication instead of retaining competing local repairs.

## Exact carrier, conventions, and claims

Let `V` be a real vector space and let
`D : HestenesKreinSplitQuaternionBridge.Datum (V := V)`. The established owner uses
`D.K` for the elliptic operator I and `D.eta` for the product operator K:

- I*I = -1;
- K*K = 1;
- I*K = -(K*I).

Multiplication means ordered composition in `Module.End ℝ V`.
No external complex scalar or complex vector-space structure is introduced.

Let B be a native `LinearMap.BilinForm ℝ V`, symmetric and nondegenerate,
with both operators B-skew: B(Ix,y)+B(x,Iy)=0 and
B(Kx,y)+B(x,Ky)=0. The proposed chain is:

1. Construct the compatibility map from the existing split datum to
   `ParaComplexConnection.ParaComplexStructure`; reuse its actual kernel
   eigenspaces and Peirce decomposition.
2. Derive both cross-pairing nondegeneracy statements from B's ordinary
   nondegeneracy and existing same-leaf isotropy, rather than assume them.
3. Construct I restricted to the positive leaf as a real linear equivalence
   to the negative leaf. Its inverse is -I, so I exchanges the two leaves.
4. Construct the native restricted form beta(u,v)=B(Iu,v) on the positive
   leaf and prove it alternating and nondegenerate.
5. In finite dimension only, derive even leaf rank from a nondegenerate
   alternating matrix, then reuse the established total-rank formula to
   prove `4 ∣ Module.finrank ℝ V`.

The final theorem must not take cross nondegeneracy, even leaf rank,
a preconstructed cross equivalence, or a fourfold dimension as hypotheses.
The zero space is allowed. Signature, connection, and manifold claims are
not part of this finite-dimensional divisibility statement.

## Owners reused

| Owner | Actual reused content |
| --- | --- |
| `Canonical.HestenesKreinSplitQuaternionBridge` | Real operator datum and ordered opposite-square relations |
| `Canonical.ParaComplexConnectionBridge` | Native kernel eigenspaces, projectors, actual Peirce linear equivalence |
| `Canonical.ParaComplexNeutralForm` | Isotropy, cross-nondegenerate datum API, rank sum and twice-leaf rank |
| `Geometry.SymplecticMetricCompatibility` (PR386) | Symplectic skew identity, exact metric comparisons and anticommutation criterion |
| `Geometry.FlatSplitQuaternionGeometry` / `Potential` | Existing four-dimensional determinant metric and actual compatible real left actions |
| Mathlib bilinear form / matrix determinant owners | Native restriction, nondegeneracy, basis matrix and determinant identities |

The bounded source survey also inspected alternate owners in `lean`, `src`,
and `proofs`, their imports and consumers, PR377's metric recovery owners,
existing octonion multiplication-defect maps, and actual metriplectic
reduction owners. No replacement of those implementations is proposed.

## Separate compatibility classes

For the common-symplectic-form construction, write
G(x,y)=omega(x,Iy) and h(x,y)=omega(Kx,y). With I symplectic and
I*K=-(K*I), the existing symplectic skew identity implies
h(Ix,y)=h(x,Iy) and h(Ix,Iy)=-h(x,y). Thus I is h-self-adjoint.
On a nontrivial space with nondegenerate h, it cannot simultaneously be
h-skew. This same h is therefore outside the both-skew hypotheses above.

The boundary lemmas will be added to the existing generic compatibility
owner, with their actual algebraic hypotheses. They do not rule out another
hypersymplectic metric or another compatible operator pair on V.

## Claim ledger and corrections

| Intake claim | Disposition |
| --- | --- |
| Opposite square laws and ordered split multiplication | Existing operator owner; reused |
| A common omega plus positivity forces anticommutation | False; PR386 gives the oblique real counterexample and the correct metric-isometry criterion |
| Universal metric comparison is I*K | Conditional; universally it is -K*I, equal to I*K under anticommutation |
| I acts complex-linearly within the positive K leaf | False; it exchanges the two leaves |
| A nondegenerate both-skew neutral triple has dimension 4m | Target of this extension, through the actual alternating leaf form |
| The common-omega neutral form is the same hypersymplectic metric | False for this same operator pair on a nonzero nondegenerate carrier; prove the precise self-adjoint/skew obstruction |
| Every nonzero cubic derivative gives curvature or permanently distinct Levi-Civita connections | Unsupported and false in general; no curved theorem is asserted |
| Nonassociative multiplication prevents associative operator composition | False; existing Zorn owners distinguish L(a)L(b) from L(ab) and construct the Clifford operator action |
| Positive metric alone gives full metriplectic dynamics | Additional maps, brackets, and degeneracy laws are needed; existing reduction owners retain those conditions |
| A causal diagram proves physical or philosophical uniqueness | Interpretation only; the dependency order below contains only actual proof implications |

## Proof dependency order

The split operator relations give the cross-leaf equivalence.
The Peirce decomposition and K-skewness give isotropy and cross separation.
Those facts, B-symmetry, and I-skewness give the nondegenerate alternating
leaf form. Matrix determinant parity gives even leaf rank. The actual
cross-leaf equivalence and existing rank sum give fourfold total rank.

Independently, common-omega compatibility gives I-self-adjointness for h;
nondegeneracy and nontriviality exclude simultaneous I-skewness.
No inference to dynamics, a global manifold, or philosophical uniqueness is
an edge in this dependency order.

## Repair and acceptance plan

PR386 CI run `44065838743` compiled all 17 inherited dependencies and the
generic compatibility owner, but found one matrix-to-endomorphism conversion
error in the oblique owner, six proof errors in the phase-space consumer,
and four selected-owner warnings. The upstream continuation `1838b7df` repairs
these source-local proofs and warnings at the unchanged pinned Lean 4.34.1 /
Mathlib d13f23b7 environment. This extension consumes that exact repair.

G-A writes the dimension candidate separately; the parent integrates it.
A-A independently reviews the actual hypotheses, proofs, nonvacuity and
scope. QA-A runs the maintained source gates and serialized native closure
check with the complete owned-declaration axiom audit. A source scan is not
a kernel certificate. Until those checks complete, this is a candidate
contract and publication remains draft.
