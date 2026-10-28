# Lie--Jordan dual transport and Peirce extraction

## Intake and scope

Sources are the user's `Pasted text(20261028-091932).txt` (archetypes
XXVI--XXIX) and `Pasted text (2)(20261028-092023).txt` (archetype XXX).
The implementation is based on `cb7482d86eadb42f2ab9c2f6f624d67b7bfe7ce4`.
This is a new, additive continuation; PR #228 and dependency pins are unchanged.
The user's Witten paper is context for earlier work, not evidence for any of
the algebraic identification claims in these two new texts.

The mathematical carrier is an arbitrary associative `R`-algebra, with native
`Module.End R A`, specialized to full `Matrix n n R`. No commutativity of
matrix inputs is required. The categorical target is the existing full matrix
`Cl11TensorTowerLimit.Limit`, never the diagonal cylinder algebra.

## Owner grounding

* `Core.JordanAssociatorRing` owns `commutator_symm_operator`:
  `[h,{s,x}] - {s,[h,x]} = {[h,s],x}`.
* `Core.JordanMultiplicationClosure.jordanLeft` owns the native linear Jordan
  operator. Its `trace_adjoint_identity` supplies cyclic trace skewness.
* Native Mathlib `LieAlgebra.ad` owns the Lie action; no replacement is defined.
* `Algebra.IdempotentProjector` owns `peirce11`, `peirce00`, `peirce10`,
  `peirce01`, complement identities and `peirce_decomposition_sum`.
* `Clifford.Cl11TensorTowerLimit` owns `Limit`, `ofStage`, `stageBond`, and
  `ofStage_apply_bond`. `Algebra.DirectLimitSuperClosureLemmas` owns the
  universal lift and injectivity theorem used by the new consumer.

The search covered the exact source names and alternate owners for Peirce,
Jordan multiplication, adjoint actions, and matrix direct limits. This is not
an exhaustive novelty claim about the entire repository.

## Explicit corrections to the intake

1. With `a = ad_h` and `j = J_s`,
   `(a-j)(a+j) = a²-j²+[a,j]`, not `a²-j²-[a,j]`.
   The general theorem retains `J_[h,s]`; no commuting-Cartan reduction is used.
2. `tau(x*y)` is a cyclic bilinear pairing. It is not by definition the BKM
   metric, and it is not the complex Hilbert--Schmidt pairing `Tr(x* y)`.
   The star-pairing theorem states the needed skew-adjoint/self-adjoint
   coefficient assumptions explicitly.
3. The dual product is formally symmetric for the bilinear trace pairing even
   when `[h,s]` is nonzero. A vanishing mixed term is not required for that fact.
4. The lower Peirce corner satisfies
   `minus p p (ad_p x) = 2 * peirce01 p x`, without the extra minus sign in
   the source table.
5. Weighted trace `tau(w*x*y)` has symmetry defect
   `tau((w*x-x*w)*y)`. Commuting inputs give a symmetric restriction;
   anticommuting inputs give a skew restriction. There is no globally symmetric
   metric with an automatically established DeWitt signature here.
6. The source's `rfl` step changing a factor containing `A` to one containing
   `B` is not a proof. The corner trace reduction is instead derived by cyclic
   rotation and the two idempotence equations.
7. The source Dirac synthesis never uses its Clifford-pair hypothesis. Here
   the doubled operator acts on the actual product module and has explicit
   Clifford generators, grading anticommutation, and an order-sensitive square.
8. In characteristic two, the doubled readouts do not recover the corners by
   division. The corner projections and their composition table remain valid
   without any characteristic restriction.

No affine connections on a manifold, Levi-Civita identification,
Amari--Chentsov tensor identification, BKM equality, flatness theorem,
Lichnerowicz formula, Fubini--Study metric, or Berry curvature is inferred from
these finite algebraic identities. They would require additional carriers and
proved compatibility maps. The algebraic colimit results do not assert a
norm completion, analytic boundary, or a new notion of Hestenes analyticity.

## Dependency poset

The order is dependency reachability, not physical time. Independent branches
are kept incomparable. Cover relations are:

```
existing associative/Lie/Jordan owners -> DualTransport
existing idempotent owner + DualTransport -> PeirceResolution
DualTransport + cyclic trace + PeirceResolution -> TracePairing
DualTransport -> CliffordDouble
PeirceResolution + existing matrix direct limit -> Colimit
TracePairing -> NoncommutingExamples
all six owners -> Synthesis
```

The import graph implements this acyclic order. Algebraic operations come first;
trace assumptions and idempotence are introduced only in the branches that
need them; the existing categorical universal property is used only in the
colimit consumer.

## New mathematical surface

* `LieJordanDualTransport`: native positive/negative endomorphisms, sum and
  difference, general products, composition obstruction, bracket closure,
  Leibniz defect, and ring-homomorphism naturality.
* `PeirceLieJordanResolution`: native indexed corner endomorphisms linked to
  existing corners, all 16 composition and 16 multiplication cases in two
  indexed theorems, complete resolution, four doubled readouts, and corrected
  positive/negative transport formulas.
* `LieJordanTracePairing`: cyclic duality, trace balance, negative-square
  factorization, formal symmetry without coefficient commutation, weighted
  symmetry/skewness, exact four-block expansions, star-compatible duality,
  and full-matrix specialization.
* `LieJordanCliffordDouble`: actual product-module endomorphisms, two
  square-one generators, an internal square-minus-one phase, odd transport,
  and the square with both signs of `J_[h,s]` retained.
* `LieJordanPeirceColimit`: the actual stage inclusion intertwines transport
  and corners, refinement compatibility, the native universal lift, and
  preservation/reflection of a nonzero evaluated composition defect.
* `LieJordanPeirceExamples`: noncommuting off-diagonal 3-by-3 coefficient
  witnesses and a non-diagonal idempotent refuting weighted-trace symmetry.

## Additive operator-level packet (PR #254)

The later operator-level packet is kept alongside the established owners above;
it does not replace their 3-by-3 regression witnesses or narrow their audit
scope. Its additional owners are `OperatorAlgebra.LieJordanDuality`,
`OperatorAlgebra.PeirceLieJordanResolution`,
`OperatorAlgebra.LieJordanTraceDuality`,
`OperatorAlgebra.PeirceTracePairing`,
`OperatorAlgebra.OperatorDiracSchur`,
`OperatorAlgebra.LieJordanDiracPair`, and
`OperatorAlgebra.LieJordanPeirceColimit`. The
`OperatorAlgebra.LieJordanPeirce` module is an import façade.

The packet retains ordered noncommutative products, explicit composition
defects, and the actual full-matrix tensor-colimit owner. Its dense 2-by-2
examples are supplementary regression witnesses nested in the existing
`LieJordanPeirceExamples` namespace; the original off-diagonal 3-by-3 and
oblique-idempotent tests remain available. The checker audits both the
pre-existing 18-module owner set and these new modules.

Corrections remain explicit: for `a = ad_h` and `j = J_s`,
`(a-j)(a+j) = a²-j²+[a,j]`; the bilinear trace is not a Hilbert--Schmidt or
BKM metric; and the complementary-corner identity has a minus sign before
`ad_p²`. The dense examples prove the positive-sign variant false. None of
these algebraic statements by itself supplies a manifold connection, a
Lichnerowicz formula, or a spectral-gap theorem.

## Verification discipline

The source contains explicit proof terms/tactics, no proof holes or extra axioms.
This sentence describes the submitted source, not a successful compiler run.
The scoped workflow compiles copied, byte-identical source imports against the
repository's exact Mathlib and Lean pins in a separate directory. It reuses
`tools/quality/check_peirce_weyl.py`, including its shared build lock and exact
module-owner transitive axiom audit. It does not mutate dependency metadata,
create cache symlinks, change existing CI gates, or bypass root-package checks.

Entry point:

```lean
import InfoGeometry.Canonical.LieJordanPeirceSynthesis
```

Scoped check:

```sh
python3 tools/quality/check_lie_jordan_peirce.py \
  --mathlib-root /path/to/exact/pinned/mathlib \
  --output /path/to/new/verification/output
```

Compiler status must be read from the actual workflow logs and `status.json`.
No source-generated verification receipt is presented as compiler evidence.
