# Opposite Peirce coupling: ground-truth contract

## Frozen intake and carriers

The two verbatim streams and their hashes are preserved beside this contract.
Their claims of machine verification are untrusted intake. The implementation
extends PR #253 from `5ba5ebe6ca55d7eea9179ef8f096a714d8d5923e`, retaining Lean
`4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The algebraic carrier is an arbitrary associative unital ring `A`. Use an
idempotent `p`, `u ∈ PeirceDecomposition.peirce10 p`, and
`v ∈ PeirceDecomposition.peirce01 p`. The concrete generated inputs are the
already owned `component10 p a` and `component01 p b`, with independent `a,b`.
Write `E = u+v`, `K = u*v+v*u`, `C = ⁅u,v⁆`, and
`γ = PeirceGrading.reflection p` only as mathematical abbreviations. There will
be no replacement commutator, corner, reflection, matrix carrier, or witness
structure. Matrix geometry uses the full `Matrix n n ℂ` and native `mulVecLin`,
`LinearMap.ker`, `PosSemidef`, and `PosDef`.

## Existing owner contracts

- `Core.PeirceDecomposition` owns the four corner sets and component maps,
  same-corner zero multiplication, opposite-corner multiplication routing,
  and support absorption.
- `Core.PeirceGrading` owns complementary native even/odd projections,
  `mem_odd_iff : x ∈ range (odd p) ↔ p*x+x*p=x`,
  `mem_even_iff : x ∈ range (even p) ↔ p*x=x*p`, reflection squaring to one,
  and parity multiplication/conjugation.
- `Core.PeirceStarCharges.odd_square` owns the square expansion of the odd
  component. Apply it to `u+v` after extracting its two corner projections.
- `Core.PeirceMatrixTracePairing.component10_eq_zero_of_trace_pairing` owns
  separation of a fixed supported matrix by every opposite corner.
- `Core.PeirceMatrixPerfectPairing` already owns the native perfect pairing
  and its dual linear equivalence. Do not recreate this structure.
- `OperatorAlgebra.PartnerEigenspaces` already owns the nonzero eigenspace
  equivalence for two composable maps; no new spectral-pairing structure is
  needed for the present kernel claims.
- `TracialCARDensity.weighted` owns a generic weighted functional. The narrow
  matrix statements use the expression `Matrix.trace (γ * x)` directly;
  weighting by a noncentral reflection is not asserted to be cyclic.
- Native Mathlib owns matrix Gram positivity, Gram vanishing, Gram kernels,
  positive-semidefinite trace detection, and the invertibility/PosDef criterion.

The existing single-input star lemma assumes self-adjoint input. The new bridge
`star (component10 p a) = component01 p (star a)` needs only self-adjoint `p`.

## Missing theorem interfaces

### `Core.PeirceCoupledCorners`

All ring statements use `hp : IsIdempotentElem p`, `hu : u ∈ peirce10 p`,
`hv : v ∈ peirce01 p` as needed.

- `left_support10`, `right_support10`, `left_support01`, `right_support01`:
  `p*u=u`, `u*p=0`, `p*v=0`, `v*p=v`.
- `component10_fixed`, `component01_fixed`, `component10_coupled`,
  `component01_coupled`, `odd_coupled`, `coupled_odd`, `coupled_square`:
  extract the corners, identify the existing odd projection, and derive
  `(u+v)^2 = u*v+v*u` from its existing owner.
- `left_jordan`, `right_jordan`, `left_bracket`, `right_bracket`:
  multiplication by `p` on either side selects `u*v`.
- `component11_jordan`, `component00_jordan`, `component11_bracket`,
  `component00_bracket`: the four exact compression equations.
- `jordan_mem_even`, `bracket_mem_even`, `reflection_mul_jordan`,
  `reflection_mul_bracket`: even support and `γ*K=C`, `γ*C=K`.
- `jordan_eq_zero_iff_bracket_eq_zero`, `jordan_eq_zero_iff_products`,
  `coupled_eq_zero_iff`: exact zero criteria, without universal nonvanishing.
- `coupled_conjugation`, `jordan_conjugation`, `bracket_conjugation`:
  reflection conjugates `E` to `-E` and fixes `K,C`.
- `star_component10`, `star_mem_peirce01`: the arbitrary-input star bridge
  under `IsSelfAdjoint p`.

### `Canonical.PeirceCouplingGeometry`

For arbitrary finite full matrices over a commutative ring, prove corner
tracelessness, trace balance of the two quadratic compressions, bracket trace
cancellation, `Tr K = 2 Tr(uv)`, `Tr(γ*K)=0`, and `Tr(γ*C)=Tr K`.
Use the existing opposite-corner separation to obtain a nonzero trace partner
for every nonzero supported matrix, and hence some nonzero coupled square.
Prove `ker (u+v).mulVecLin = ker u.mulVecLin ⊓ ker v.mulVecLin` and
`ker K.mulVecLin = ker C.mulVecLin` from the support and reflection laws.

### `Canonical.PeirceCouplingPositivity`

For full complex matrices with a star projection `p` and `u ∈ peirce10 p`,
the adjoint corner is in `peirce01 p`. Prove Hermiticity of `u+uᴴ` and
`⁅u,uᴴ⁆`, the Gram-square identity, and native positive semidefiniteness.
Prove the precise zero/trace/kernel conclusions:

```
u*uᴴ+uᴴ*u = 0 ↔ u = 0
0 < trace (u*uᴴ+uᴴ*u) ↔ u ≠ 0
ker (u*uᴴ+uᴴ*u).mulVecLin = ker u.mulVecLin ⊓ ker uᴴ.mulVecLin
(u*uᴴ+uᴴ*u).PosDef ↔ ker u.mulVecLin ⊓ ker uᴴ.mulVecLin = ⊥
```

The direct Gram positivity lemma itself needs no support hypothesis. Star
projection and corner membership justify the relation to the coupled square.

### `Canonical.PeirceCouplingExamples`

Reuse PR #253's dense `P,S`. Prove that `u = component10 P S` has repeated
row `(-13,2,11)/9`; its positive coupled square has trace `196/9`, is nonzero,
and annihilates the nonzero vector `(3,-8,5)`. Prove it is not positive definite.
For the independently chosen opposite corner `-uᴴ`, prove negative Gram square,
negative trace, and failure of positive semidefiniteness. Both pairs of corner
operators, `(u,uᴴ)` and `(u,-uᴴ)`, fail to commute; the projection is nondiagonal.

## Proof prerequisite partial order

Existing support routing → corner extraction → existing odd-square expansion
→ compression and reflection duality → co-vanishing and equal kernels.
Support splitting independently gives the coupled-kernel intersection.
Cyclicity plus compression gives trace balance. The native opposite-corner
pairing gives existence of a nontrivial partner. Star exchange plus native
Gram results gives positivity and exact zero/trace detection; combining this
with kernel splitting gives the PosDef criterion. Full matrix witnesses consume
those theorems. Edges are proof prerequisites, not physical causation.

## Intake classification and scope

- Corner nilpotency and grading: theorem-backed existing owners.
- Independent opposite-corner reflection/compression/trace identities: local
  mathematical targets, pending kernel verification.
- Positive Gram conclusions: `[bucket_2_conditional]` on adjoint pairing.
- Arbitrary positivity and a positive-definite inference from nonzero coupling:
  `[countermodel_found]` candidates, to be promoted only after Lean proofs.
- `[E,E²]=0`: universal associativity, not a new cubic polynomial or Drazin law.
- Particle interpretations, spontaneous symmetry breaking, Yang–Mills gap,
  curvature, gravity and topological wrapping: `[bucket_3_open_debt]`; no such
  structures or conclusions enter the theorem statements.

Final acceptance requires exact-source compilation, native Lake build, semantic
and constructivity review, and a complete ownership/axiom audit. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted foundational axioms.
