# DeWitt real carry: theorem contract

## Source and scope

Intake: the user's 8 November 2026 DeWitt tetractys / real parafermion draft,
including both proposed Lean versions. The source proposes, verbatim,
`J := S_P * Phi`, `zetaReal := P2 * Phi2 + (1 - P2) * J1 * Phi2`,
`zetaReal^2 = J1`, and the numerator
`(1 - X^2) + zetaReal * X * (1 + X^2)`.
It also claims an integral eighth root, reflection inversion, Brown–Gauss
identities, exact order, unitarity, Clifford/Lie identifications, dimensions,
and a causal poset. The earlier code has proof holes; the later version assumes
an ambient commutative ring for the rotor. Neither supplied verification claim
is accepted as evidence.

Base: upstream `main`, `3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`.
Lean and Mathlib pins remain unchanged.

## Existing owners

- `OperatorAlgebra/PeirceSpine/Basic.lean`: `invS`, `conePlus`, `coneMinus`,
  `genPhi`, `genJ`, `genV`, corner multiplication and `peirce_nf`.
- `OperatorAlgebra/PeirceSpine/Tetraktys.lean`:
  `archetype_A2_peirce_cartan_grading_and_tangent_closure` and
  `archetype_A3_nilpotent_cones_and_tetraktys_table` already prove the
  unnormalized involution and multiplication relations.
- `Canonical/CyclotomicExplicitMatrixBridge.lean`: an existing integral
  companion of `x^4+1`, with fourth/eighth-power identities. The new witness
  must connect the carry construction to it rather than duplicate the claim.
- Native Mathlib `Commute`, `Units`, `orderOf`, matrix operations and
  `orderOf_eq_prime_pow` supply the standard carriers and interfaces.

The algebraic owner search included all tracked Lean files for the proposed
names, carry formulas, rotor terminology, related Peirce and Clifford owners,
and their imports. No existing general binary-carry square law or quartic
rotor numerator product was found in that search.

## Exact dependency order

1. In `[Ring B]`, `P*P=P` gives complementary corners and the existing grading.
2. Normalizing `genPhi P A C * genPhi P A C = 1` yields `genV=1`, `genJ^2=-1`,
   the ordered normalized products, and both conjugation laws.
3. For a second idempotent `p` and involution `f` with
   `f*p=(1-p)*f`, any `a` commuting with `p` and `f` has
   `(p*f+(1-p)*a*f)^2=a`. Commutation is local, not global.
4. Specialize `a*a=-1` to obtain fourth/eighth powers, an explicit two-sided
   inverse and a native unit. Add `(-1:B) != 1` only to derive exact order eight.
5. An involution `s` commuting with `p,f` and satisfying `s*a=-(a*s)` gives
   inverse conjugation by `s*f`. Conjugation by `s` alone is not enough.
6. For `z^4=-1`, `x^4=1`, and `Commute z x`, prove the two Gauss identities,
   annihilation of parity products, and both numerator products equal to `4`.
7. Primitive star laws `star p=p`, `star f=f`, `star a=-a` identify the carry
   inverse with its actual star. The carry belongs to native `unitary B`.
   With `[Invertible (2 : B)]` and the bond star law, its normalized quartic
   rotor also belongs to `unitary B`, derived from the primitive local data.
8. Integral matrices instantiate the construction, reflection and exact order;
   the abstract identities are not restricted to those matrices.

## Semantic corrections and remaining boundaries

- `[Ring B]` does not supply a real scalar field, a basis, a dimension, a star
  operation or invertible `2`. All such assumptions must be explicit.
- `z^4=-1` implies `z^8=1`; exact order eight needs `-1 != 1`.
  Likewise `x^4=1` asserts order dividing four.
- `N_+` and `N_-` are defined by Peirce products without division. Formulas
  using one half require `2` invertible. The tetrad `{1,S,Phi,J}` is not a
  basis of all `Mat_2(Int)`; its integral span has parity restrictions.
- The anticommuting square-positive pair `(S,Phi)` has signature `(2,0)`.
  The pair `(S,J)` has signature `(1,1)`. Abstract real algebra isomorphisms
  do not identify these quadratic generating spaces.
- The equation `1+2+3+4=10` does not prove any dimension, Lie algebra
  isomorphism, conformal-group identification, or formal partial order.
- Scaled two-sided inverse identities are not adjoint identities. The new star
  theorems explicitly add matching primitive star laws; normalized rotor
  unitarity separately assumes an inverse for `2`. The carry's unitarity
  itself remains division-free.
- A single quartic generator supplies no adjacent-generator Yang–Baxter
  relation or parafermion braid representation. Those remain separate goals.
- An internal complex structure need not be central. Its existence does not
  make ordinary scalar complexification inconsistent or erase distinctions.
- No analytic, topological, physical condensation, or infinite-limit theorem
  follows from this finite algebraic work.

## Validation plan

Compile the unchanged selected imports and every new owner with the exact
pinned native compiler; scan for placeholders; inspect every new theorem's
axiom dependencies; independently audit statements and the concrete witness.
Use the repository lock for every compiler invocation. Report scoped checks
separately from the root package build, which currently fails on the missing
`external_refs/homotopy-hypothesis-lean4` dependency. No dependency pin, root
Lake configuration, existing gate or unrelated source is to be changed.
