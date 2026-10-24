# Nilpotent–Peirce–Drazin–Moore–Penrose verification

Toolchain: pinned Lean v4.34.1.

## Current revision: 2026-10-24

Independent source review requested removal of two unused conjunction packets,
`square_zero_mp_reflections` and `drazin_mp_joint_cartan_synthesis`.
They have been removed; consumers use their existing component lemmas directly.
Copyright headers were added to PeirceGrading and NilpotentCartanRegression.
The earlier build counts and hashes below describe the **pre-removal** snapshot;
the revised sources passed independent A-A and QA-A replay on 2026-10-24.
The current four-file build completed 3818 jobs; all 84 declarations (59 + 8 + 17)
passed the transitive axiom audit, with stable source/pin hashes and no warnings
in the four selected files. Receipt: `/tmp/qa-a-cartan-final-dhdkijmx/result.json`.
The current Core.All is covered by this replay, not by its historical hash below.

## Mathematical contract and ownership

The carrier remains an arbitrary associative `Ring A`; star-specific results
add `StarRing A`. No dimension, diagonalizability, positivity, or global inverse
existence assumption is introduced.

- An **inner inverse witness** `d * b * d = d` produces the two native
  `IsIdempotentElem` supports. If `d * d = 0`, the domain support annihilates
  the range support. Normalizing `b` to `b * d * b` gives a reflexive pair.
- Penrose laws use the existing
  `InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse`: the two reflexive
  equations and self-adjointness of both products. The existing
  `ProjectionSectors.mp_supports` and `SquareZeroMoorePenrose` results supply
  native `IsStarProjection`, reverse annihilation and square-zero of the inverse.
- An idempotent produces `reflection p = 2 * p - 1`, its square-one identity,
  and its two support actions. Self-adjointness upgrades this to membership
  in Mathlib's `unitary A`. A difference is proved tripotent only under
  two-sided orthogonality, including the square-zero Penrose case.
- `InfoGeometry.Core.PeirceGrading.even` and `.odd` are native `ℤ`-linear
  endomorphisms on **A itself**, formed from the existing
  `PeirceDecomposition.component11` and `.component00`. Their ranges are
  complementary native submodules. `decomposition` is the actual linear
  equivalence with their product. All associative-product and Lie-bracket
  parity laws are proved without restrictions on two.
- `conjugation` acts by `reflection p * x * reflection p`. Its full native
  `Module.End.eigenspace` identifications require exactly the stated
  injectivity of `fun x : A => (2 : ℕ) • x`. The Peirce direct sum itself
  does **not** require this hypothesis.
- The existing canonical Drazin predicate asserts
  `x*d = d*x ∧ d*x*d = d ∧ x^(k+1)*d = x^k`.
  Its `projection`, `fittingNilpotentPart`, commutation and nilpotency lemmas
  are reused, not redeclared. The exponent is a witness, not a minimal index.
- Joint Drazin/Penrose applications use the existing Drazin projection and
  nilpotency lemmas, `drazin_even`, and native `mp_supports` directly.
  The `support_anomalies` theorem proves the algebraic identities for arbitrary
  support candidates without Penrose hypotheses. Star-projection conclusions
  separately require the Penrose laws; no wrapper packet combines these facts.
- `corners_sq_zero` proves the return to square-zero corners. It does not
  manufacture an inverse for these corners. No nontrivial cycle of a partial
  order, positivity-based Cartan involution, or unconditional inverse existence
  is asserted.

The historical `NilpotentToCartanDrazinMPPoset.lean` path and namespace remain,
but the broken duplicated inverse/projection structures and operation wrappers
have been removed. Search of `lean`, `proofs`, `scratch`, `tests`, and `lib`
found no other Lean consumers of the old namespace before integration.
`Core/All.lean` imports the repaired development and its regression module;
`AllExhaustive.lean` imports `Core.All` and is imported by `InfoGeometry.All`.

## Earlier checked scope (2026-10-23, before packet removal)

| Module under `InfoGeometry.Core` | All declarations audited |
| --- | ---: |
| `PeirceGrading` | 59 |
| `NilpotentToCartanDrazinMPPoset` | 10 |
| `NilpotentCartanRegression` | 17 |
| **Total, including generated declarations** | **86** |

The shared-lock build of `InfoGeometry.Core.All` succeeded (3785 jobs), including
all three modules together. Final log: `/tmp/nilpotent-cartan-core-all-final.log`.

`tools/infra/axiom_check.lean` replayed every declaration in all three module
artifacts and inspected transitive axioms. All passed; only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. Final log:
`/tmp/nilpotent-cartan-axioms-final.log`.

A source-aware scan using `tools.quality.audit_constructivity.strip_comments`
(masking comments, strings and quoted identifiers) found no active
`sorry`, `admit`, `sorryAx`, `axiom`, `postulate`, `unsafe`, `partial`, or `#exit`
in the three modules or modified umbrella. Staged whitespace checks passed.

The regression module proves:

1. Square-zero `2 : ZMod 4` has no inner inverse.
2. In characteristic two the nonzero identity lies in both reflection
   eigenspaces but not in the odd Peirce submodule.
3. A rational matrix Penrose pair has nontripotent support difference.
4. The joint Drazin/Penrose hypotheses have an example with nonzero anomaly.
5. A nonzero square-zero Penrose pair exists.
6. A reflexive square-zero pair exists as native endomorphisms of `V × V`
   without a finite-dimensional assumption, including `V = ℕ → ℚ`.

**Limits:** no full-superproject default-target build or global clean-baseline
certification is claimed. The successful Core umbrella build replays existing
warnings in other owners (including MoorePenrose, DiracPeirceSuperalgebra and
ProjectiveSimplex), plus existing dependency-local-change notices. None of the
four touched Lean files emits a warning. Unrelated concurrent work was not
repaired or committed; these changes are staged, with no commit created.

## Reproduction

Inspect active compiler processes first, then serialize through the shared lock:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Core.All
```

Under `tools.build_lock.acquire_build_lock(None, description, block=True)`, run:

```sh
lake env lean --run tools/infra/axiom_check.lean \
  .lake/build/lib/lean/InfoGeometry/Core/PeirceGrading.olean \
  .lake/build/lib/lean/InfoGeometry/Core/NilpotentToCartanDrazinMPPoset.olean \
  .lake/build/lib/lean/InfoGeometry/Core/NilpotentCartanRegression.olean
```

## Earlier verified source SHA-256 (not the current revision)

Paths are relative to `lean/InfoGeometry/Core/`.

```text
f21517ad867e0e21df426645f6607567958acac4159b845b199ee9220b7a61b0  PeirceGrading.lean
e65a3de8a6158c250022c21d1a3a7b5a7d8284104d971ff6c71d3e7b5801186b  NilpotentToCartanDrazinMPPoset.lean
510944b9b19b39ecf049ccf88d5d06d36048484faae2fcdb2d996155df0f4e9c  NilpotentCartanRegression.lean
5a529d9b9c4e5fe39993cef5db45ce27e322ed95270e57aa9b4b8b1f506880ec  All.lean
```

## Final independent replay, 2026-10-24

Two additional noncommutativity lemmas bring the three-owner count to 86. The updated regression owner has 19 axiom-clean declarations.
The five rechecked owners passed with 81 declarations total. Exact Core.All and
InfoGeometry.All builds passed (9011 and 26980 jobs respectively), with stable
seven-source/pin hashes and no scoped warnings. Existing imported warnings remain.
Receipt: `/tmp/qa-a-catto-retry2-j1uswpr6/result.json`. Aggregate compilation is not an all-imported-declaration
axiom audit or clean-release certification.

Current selected source hashes:

```text
dbaedda7dd9de84e39a68b9fde31379881b74c80f643b9353d381dc505cf72b3  lean/InfoGeometry/Canonical/CattoGurseySplitBasis.lean
f96eaddc904397bd2caf18e06490d2547675898abeb818cd9b8d85b95367ddad  lean/InfoGeometry/Canonical/CattoGurseyBlockGrading.lean
6ca073eca2f944438c242a075f59899b33b59b85a9b83dd7377d98cdbba7bd3f  lean/InfoGeometry/Superalgebra/CattoGurseyOctonionicHadronicSuperalgebra.lean
2d6caf71e4674dc8788b7adffdadf91040790f8d310597480ba2bc5f761e7133  lean/InfoGeometry/Core/BosonFermionRegression.lean
cc902922dd30965ef0ddfa2ed68f501ecdefa1ab6bbc03faeed89c81604ce8c9  lean/InfoGeometry/Core/NilpotentCartanRegression.lean
7f6fcf1befcfab57bb3a4ffe11f0855fb4248302e178171e4c2c8044406f16ac  lean/InfoGeometry/Core/All.lean
fbe04fa6993ead97420c2393e0fe11716accfe5f3a34dad5691a0762c2e11fa1  lean/InfoGeometry/All.lean
```
