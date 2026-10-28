# Clifford products and Peirce odd pairs

## Intake and theorem contract

The two user uploads dated 2026-10-28, `Pasted text(20261028-091154).txt`
and `Pasted text (2)(20261028-091358).txt`, supply proposed archetypes XIX–XXV.
Their SHA256 digests are respectively
`dda96780099b61288d924814c771da662b0f5a740638607daa0a08c82e9c40cf`
and `c3e4a1075d4c0e5fb2e9cf943f16d82dc2dd75a0bbf0e08aa27a532ad588da3c`.
The uploads remain the provenance record; their assertion of compilation is not
verification evidence. This work follows `skills/epistemic-compilation/SKILL.md`.

Carrier: full `Matrix n n R`, with finite decidable `n` and `Ring R`.
Only adjoint results need `StarRing R`. Multiplication order is retained.
The Clifford hypotheses are `a*a=1`, `b*b=1`, `a*b+b*a=0`.
No commutation between coefficient operators X and Y is assumed.

The principal extension is a bilinear product formula for
`(a*X+b*Y)*(a*U+b*V)`. Without cross commutation, its four correction terms
are `a*[X,a]*U + a*[X,b]*V + b*[Y,a]*U + b*[Y,b]*V`.
When X and Y commute with a and b, the product becomes
`X*U+Y*V+(a*b)*(X*V-Y*U)`; U and V remain arbitrary.
Specializing U,V gives the two squares and both ordered cross products,
and adding/subtracting them gives doubled sum/difference identities.

For an idempotent P and arbitrary A, use the native linear map `odd P` and
reflection from `Core.PeirceGrading`. With D=[P,A], M=odd P A,
prove `{D,M}=0`, `D²+M²=0`, `M+D=2 P A(1-P)`,
`M-D=2 (1-P) A P`, square-zero of both sums, and their anticommutator
`{M+D,M-D}=4 M²`. With self-adjoint P,A, these two sums are adjoints.

## Existing owners read and reuse

- `NCG.NonCommutativeFredholmIndex`: definitions `commutator A B = A*B-B*A`
  and `anticommutator A B = A*B+B*A`; theorem
  `commutator_sq_of_anticomm_zero`: `{γ,Y}=0 -> [γ,Y*Y]=0`.
- `Core.PeirceGrading`: `odd_apply`, `reflection_sq`, `commutator_odd`,
  `odd_reconstruction`, `corners_sq_zero`, `odd_anticommutes_reflection`.
  In particular `odd P A=reflection P*[P,A]=[P,[P,A]]`, and each directed
  corner is square-zero. No replacement grading API is introduced.
- `Clifford.LorentzianBivectorSignatureBridge.positive_bivector_sq_neg_one`:
  `a²=b²=1` and `{a,b}=0` imply `(a*b)²=-1` in any associative ring.
- `Superalgebra.KahlerDiracWeitzenbockSynthesis.diracOperator₂_sq_weitzenbock`
  already owns the two-generator square on `Module.End R Ω`, under the same
  Clifford relations and four cross commutations. The new bilinear formula
  extends this algebraic pattern with arbitrary right coefficients and exact
  noncommutation corrections. The matrix square corollary feeds polarization;
  it is not presented as a new geometric Lichnerowicz theorem.
- `Canonical.InformationalLichnerowicz` and
  `Canonical.ChiralHodgeLichnerowiczBridge` concern continuous endomorphism
  transport derivatives and explicit compatibility data. They are separate
  carriers, not silently identified with this matrix calculation.

## Dependency order and scope

The source proof dependencies give the order:
Clifford relations -> product with defects -> commutant product -> four
specializations -> sum/difference identities. Independently, native Peirce
corners and reconstruction -> opposite squares and anticommuting pair ->
square-zero charges -> paired anticommutator and conserved square; the star
branch gives adjoint charges. Bivector adjoints and conjugation follow from
the native square theorem and Clifford relations.

This is a source-level dependency order, not an independently formalized
causal-poset carrier. Context preflight found no generated declaration-DAG
or InfoTree index in this checkout; no graph freshness is asserted.

Boundaries: factor reversal is not time reversal; a square-minus-one element
does not alone construct the quaternion algebra. Sum/difference of operator
squares does not establish ellipticity, hyperbolicity, a manifold metric,
Laplace–Beltrami, scalar curvature, or the geometric Lichnerowicz formula.
The Peirce charge is a nilpotent differential. The anticommutator of the two
charges may be nonzero; a single charge square is zero. No particle-hole
symmetry, physical BdG model, or analytic SUSY index is asserted. There is no
division by two, so doubled readouts remain valid even in characteristic two;
recovering undoubled quantities requires extra hypotheses.

## Verification

Pending kernel, axiom, vacuity, and independent acceptance gates.
