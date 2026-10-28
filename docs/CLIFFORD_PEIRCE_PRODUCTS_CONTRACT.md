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
corner nilpotence -> square-zero charges; reconstruction and native parity ->
pair anticommutation. These two branches imply opposite squares, which imply
the paired anticommutator. Pair anticommutation also gives the conserved
square; the star branch gives adjoint charges. The native bivector square
theorem supplies its unit, while adjoint and conjugation results use the
Clifford relations directly.

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

`[kernel_verified]` for all 29 new theorems (16 Clifford products and 13
Peirce-pair results), within the finite algebraic scope above.

- Verified source commit: `7a3ea8d5439dee90c9c15e8c932f49331555710d`.
- Checked PR merge: `dfa2af03cd28704ed1661e7c864b3e97a551b136`.
- Successful [run 40669221464](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40669221464),
  job `122751457176`, executing `bash scripts/quality/check-clifford-peirce.sh`.
- Official Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`;
  Lake `5.0.0-src+5045d00`; pinned mathlib
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Eight modules compiled sequentially with fresh project oleans and the shared
  build lock: FiniteSpinAlgebra, PeirceDecomposition, PeirceGrading,
  NonCommutativeFredholmIndex, LorentzianBivectorSignatureBridge,
  CliffordMatrixProducts, PeirceOddPair, CliffordPeirceAudit.
- Exact-set axiom gate: `AXIOM_AUDIT_PASS: 29 declarations`; each footprint
  contains only `propext`, `Classical.choice`, and `Quot.sound`.
- `semantic_vacuity: 0`; no Lean warnings in the focused check. New source has
  no placeholders, custom axioms, unsafe declarations, or `native_decide`.
  The local staged proof-proxy gate also passes.
- Independent semantic audit and a separate acceptance reviewer returned
  `ACCEPTED_WITH_LIMITED_SCOPE`. The acceptance reviewer independently read
  the successful job logs, checked all 29 axiom reports, and matched all three
  source hashes to the inspected files.
- Final verification documentation changes do not alter the checked Lean
  sources, workflow, or verification script. This is not a full root Lake build.

Checked SHA256 source digests:

| File in `lean/InfoGeometry/NCG/` | SHA256 |
| --- | --- |
| `CliffordMatrixProducts.lean` | `34ea150486bba0e53ea13cc23d37132159c85e235be1debfdc885f0c56c0eff6` |
| `PeirceOddPair.lean` | `2757611981cc13b5a41d9d36a1d7596a04ff5d8f03ec2d72776e704e00d8ca5c` |
| `CliffordPeirceAudit.lean` | `13bf927a2554b8938a0fe03cf470d6ff6b139050e8ff35ad922308a073f5bc3b` |

Separate repository-wide checks are not being represented as passing:
at source `18253fe9faf82d676f4c2eb4c6e050358cad88b8`, style run
40665096410 stops at the existing filename case collision
`Canonical/KRDualityCascade.lean` versus `Canonical/KrDualityCascade.lean`;
Sorry Gate run 40665096270 cannot start its build because `lake` is absent
from that runner. Neither reaches the new proof modules. These unrelated
infrastructure defects are outside this mathematical change.
