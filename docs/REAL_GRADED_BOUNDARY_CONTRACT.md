# Real graded boundary compilation

## Source, reuse and branch ownership

This package extracts the four uploads without promoting their physical labels:

| Source | SHA-256 |
|---|---|
| Pasted text(20261028-120949).txt | 70a02c2bfae6f92aa8a21c60738777361541a52ec546ad8770474ffda75323af |
| Pasted text (2)(20261028-121051).txt | da48160c8e6e84b3ba8696a97520282e8b4fd8e604346d215f8ea03d37602180 |
| Pasted text (3)(8).txt | 9accca3218bb34d7bbc033e6c0c6ed17ad9718b526cd2e2d835c139d9974c308 |
| Pasted text (4)(2).txt | c9ea1b3660df958f1492aa1bb7aa48a1a59abb84439546bd958ba1180cfe8c85 |

The dependency is PR #250 at f550271b141afb44c0ff52fec81eb1552a45ebca.
Its actual LieJordanEndomorphisms and PeirceLieJordanResolution owners are reused,
not copied. This branch does not alter that parent or PRs #227/#248/#255/#256.
The parent is a draft; only the selected imported owners are checked here,
not its whole branch. No merge is performed.

Source searches also inspected Core.IdempotentCartan, Core.PeirceGrading,
Core.PeirceDecomposition, Algebra.IdempotentProjector,
Canonical.ChiralSuperderivationColimit, Core.DiracPeirceSuperalgebra and
OperatorAlgebra.InnerConjugation. The existing Boolean-tagged superderivation
already has a parity-flipped square theorem. The addition here is an untagged
endomorphism on the full algebra, a concrete Peirce grading, a native short
complex, and a proved positive-pairing adjoint. No graph service was queried;
no declaration-DAG freshness is claimed.

## Source corrections (not silent replacements)

1. The first upload's prose says the Jordan boundary squares to zero on every
   matrix. Its actual code proves mixed Lie/Jordan cancellation instead.
   With L_q(x)=qx-xq and J_q(x)=qx+xq:
   L_q^2=J_(q^2)-2(x -> qxq), J_q^2=J_(q^2)+2(x -> qxq).
   Thus q^2=0 does not make either ordinary action square-zero. The mixed
   compositions L_q J_q and J_q L_q do equal L_(q^2).
2. The second upload's mixed difference is false:
   L_a J_b-L_b J_a = J_(ab-ba)+2(x -> axb-bxa).
   The actual operator commutator L_a J_b-J_b L_a=J_(ab-ba) is already in #250.
   These have different second terms; no factor has been dropped here.
3. The source's mixed sum equals L_(ab+ba), as stated. It is not automatically
   the positive Hodge Laplacian. The adjoint construction below is distinct.
4. The trace identity for axb+bxa holds for every matrix x, not just even ones.
   Positivity requires b=a^T; trace preservation requires ab+ba=I.
   The implementation proves positivity preservation, not a complete-positivity
   amplification theorem and not a normalized channel without hypotheses.
5. The last two uploads supply valid algebraic reciprocal-derivation and
   quadratic conservation identities. An ad_P two-cycle is not a periodic
   real-time oscillator. In particular a real evolution j'=e,e'=j is hyperbolic.
   No frequency, spacetime signature, spin, mass or particle identification is
   inferred from the ring identities. The square operator need not be scalar or
   central in the ambient matrix algebra, so no automatic Cl(1,1) representation
   over the original scalar field is asserted.
6. The advertised two-line normalizer is not proved a complete Knuth--Bendix
   procedure. Each concrete theorem is individually checked by Lean. We do not
   claim that every identity in the input has already been kernel verified.

## Native carrier and exact operator contracts

All general operators live in Module.End R A, where R is a commutative scalar
ring and A is an arbitrary associative R-algebra. A is not assumed commutative.
All concrete metric carriers and regressions are Matrix (Fin 4) (Fin 4) real.
No complexification, diagonalization or simultaneous commutativity is used.

The actual maps L_q and J_q are inherited from #250. sandwichOp is ordered
left/right composition, and crossTransport(a,b)(x)=axb+bxa.
LieJordanBoundaryComposition proves both mixed sums, the corrected difference,
both pure sums, and their two- and four-fold combinations as endomorphism
identities. The existing lie_lie and lie_jordan laws are not duplicated.

For an involutive algebra automorphism theta and theta(q)=-q, define
  d_q(x)=qx-theta(x)q,
  c_q(x)=qx+theta(x)q.
Then d_q obeys the twisted Leibniz law on all elements, reverses parity, and
satisfies d_q^2=L_(q^2). If q^2=0, its native range lies in its kernel and
ShortComplex (ModuleCat R) is constructed with both differentials d_q.
The concrete theta is the scalar-compatible upgrade of the existing
IdempotentCartan.reflectionConj, with S=2P-I and theta(x)=SxS.
For q=P a (I-P), oddness and q^2=0 are derived, not supplied separately.

Two minus actions satisfy {d_q,d_r}=L_(qr+rq). In contrast
{d_q,c_r}=J_(qr+rq). For real self-adjoint P, r=q^T gives the actual
Frobenius adjoint:
  tr((d_q x)^T y)=tr(x^T c_(q^T) y).
Consequently the adjoint Laplacian is
  D=d_q c_(q^T)+c_(q^T) d_q=J_(qq^T+q^Tq),
with exact nonnegative energy
  tr(x^T D x)=tr((d_q x)^T d_q x)+tr((c_(q^T) x)^T c_(q^T) x).
Its actual native kernel is ker(d_q) inf ker(c_(q^T)).
No manifold differential forms, de Rham comparison, completed Hilbert space,
or full Hodge decomposition/isomorphism with homology is asserted.

PeirceBoundaryDynamics retains ad_P^3=ad_P as an endomorphism identity, the
unscaled corner recovery, conditional Leibniz conservation equivalences, and
weighted noncommutative commutators. The symmetric product centralizes the two
square-zero generators, not every ambient operator.

## Regressions and dependency poset

The support is nondiagonal and orthogonal. The forward and reverse arrows have
all entries nonzero, are genuinely noncommuting, and couple two internal modes.
They provide counterexamples to the Jordan-square, Lie-square and cross-swapped
mixed-difference claims, and to positivity for an independently signed reverse
arrow. The corrected global differential is both nonzero and square-zero.
These are full matrix calculations, not scalar representations of an operator.

PeirceBoundaryOrder constructs a finite native PartialOrder by inclusion of
explicit prerequisite sets. The differential and metric-adjoint stages are
incomparable prerequisites of the energy/kernel result. Composition identities
and the global differential are separate descendants of the operator layer.
This is a dependency specification, not the extracted full declaration graph.

## Verification

Pending the actual scoped workflow. The local authoring environment has no Lean
executable and cannot resolve external hosts. The workflow reuses the existing
exact-pin source-closure compiler and native Lean.collectAxioms audit. It checks
the two reused parent owners and all six new owners, including generated/private
declarations, under the shared build lock. Root toolchain, Lake manifest and
dependency pins are unchanged. A successful focused check is not a full root
build, independent human review, or an all-green-CI claim.
