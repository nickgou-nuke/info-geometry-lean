# Klein hierarchy native repair candidate

## Provenance and scope

This is a focused repair of
`lean/InfoGeometry/Canonical/ZornCliffordKleinHierarchy.lean` for the actual
diagnostics from scoped CI run `45416776463`, diagnostic run
`c73ae23678dd44f398d46c2a8ef7184f`.

The published branch source is at
`c97caca572514f128e846212ca30f050414dabac`. GitHub Actions reports the checked
event revision `4fdd01ba6f8923482423b4a7838fe1f037b955c9`. The owner bytes are
identical: the restored checkout, preserved original candidate, and diagnostic
`report.sources` all give the original owner SHA256 below.

| Artifact | SHA256 |
|---|---|
| Original owner | `ea37f4082661ebee3c7519e290509c0162e51b9e4e2f61acca76e1db436cc5ba` |
| Repaired candidate | `d316d756b9c856903a7ff9859a94b587fcdcd35a56b55b5c925d6ced8840a05f` |
| Unified patch | `245589046466a58fee07f031fed347e902a2ad6ada2901a08f923edfd1018869` |
| Original owner diagnostic log | `b5459cf689175c3690e8d0320d01956ed0096c1e77ab671980435e680625fc1e` |

Files in this candidate directory:

- `ZornCliffordKleinHierarchy.lean`: complete owner replacement candidate.
- `klein-native-repair.patch`: focused unified diff.
- `REVIEW.md`: this diagnostic and proof-scope ledger.

No public signatures, assumptions, carriers, imports, normalizations, or
mathematical claims change. All operators remain in the actual associative
endomorphism algebra of the real sixteen-dimensional Dirac carrier.

## Complete diagnostic ledger

Line references here refer to the original owner as named in the CI log.

| Original site | Observed diagnostic | Candidate response |
|---|---|---|
| 46, 53, 60, 67 | Four `letI` style warnings in proposition proofs | Use the compiler-recommended `let` form for the same finite-dimensional instance. |
| 69 | `letI` style warning for invertibility of real 2 | Use `let` for the same `Invertible` value. |
| 110 | Gamma readback leaves an applied linear-map record unreduced | `change` first exposes the actual pair `(x * t, zornConj x * s)`. |
| 112, two warnings | Product/conjugation bridge simp arguments unused because the application stayed unreduced | Keep those two needed bridge lemmas after the new `change`; remove the obsolete definition-unfolding list. |
| 124 | Chirality scalar field leaves a record equality instead of scalar/negation compatibility | Prove the first product component by `rfl`; expose `-(r • Ψ.2) = r • (-Ψ.2)` and use `smul_neg` in reverse. |
| 131 | `diracChirality_sq` reports a dependency using a proof placeholder | This is downstream of the failed `diracChirality` definition. Repair that definition; do not add or change any placeholder. |
| 275 | Bivector/gamma expansion leaves scalar `-1` factors inside products | Distribute scalar actions, both product/subtraction forms, and scalar subtraction; normalize association and close by `abel`. |
| 276 | Reverse `smul_sub` argument unused | Replace the failed factoring approach with forward `smul_sub` distribution. |
| 316 | Bivector/bivector derivation expansion has the same residual-product obstruction | Distribute products and scalars, including `smul_add`, normalize association, and close by `abel`. |
| 317 | Reverse `smul_sub` argument unused | Use the forward distribution required by the repaired expansion. |

These are all four errors and all ten warning messages in the supplied owner
log. This table records intended repairs, not a claim that the candidate has
already passed native compilation.

## Exact proof mechanisms

### Gamma application

The existing `diracGamma` is a linear-map record whose function evaluates to

```lean
(x * t, zornConj x * s)
```

An explicit `change` performs this definitional reduction before using
`canonicalVectorEquiv_mul` and `canonicalVectorEquiv_zornConj`. Consequently
the proof applies the existing product-preserving readback, without constructing
a new multiplication or coercion bridge.

### Chirality scalar compatibility

The second component is proved at the abstract module interface:

```lean
change -(r • Ψ.2) = r • (-Ψ.2)
exact (smul_neg r Ψ.2).symm
```

This avoids broad simplification that unfolds native Zorn negation into a
record before scalar distribution has been applied. The `change` also removes
the definitional identity-ring-hom coercion from the constructor field target.

### Associative operator rearrangements

For the gamma commutator, write `X = Γ(x)`, `Y = Γ(y)`, `Z = Γ(z)`, and
`a = 1/2`. The repaired first calculation is the genuine ring/module identity

```text
(a • (XY − YX))Z − Z(a • (XY − YX))
  = a • ((XYZ − ZXY) − (YXZ − ZYX)).
```

Distributing multiplication and scalar actions first reduces both sides to
the same signed sum of scalar multiples of four ordered triple products.
`abel` rearranges only their additive group; it never commutes multiplication.
The existing `hxy` and `hyx` then supply the native Clifford commutator law,
with the original unhalved polar form unchanged.

For the bivector closure, let `D = realDiracBivector x y`. The repaired
calculation expands

```text
[D, a • (UV − VU)]
  = a • ([D,U]V + U[D,V] − [D,V]U − V[D,U]).
```

After distribution and reassociation, the internal terms cancel additively.
The already constructed `hu` and `hv` are then applied. The existing final
module-only calculations remain unchanged; their goals do not need further
distribution of multiplication over subtraction.

The proof explicitly uses `_root_.sub_mul` and `_root_.mul_sub`, because this
owner opens `CanonicalVectorMatrixBridge`, which defines identically named
lemmas for the nonassociative Zorn carrier. Here the relevant carrier is
`Module.End`, so the root ring lemmas are the intended interfaces. Only
associativity, distributivity, and the module laws are used; no commutative-ring
assumption is introduced for operators.

## Validation status

Performed: read the actual CI log, checked the original owner identity against
the diagnostic receipt and restored checkout, inspected relevant imported
definitions, compared the candidate source diff, and recorded hashes.

Not performed: Lean compilation, Lake build, tests, axiom audit, Python syntax
validation, or local diagnostic execution. No tracked repository source,
dependency cache, or GitHub state was modified by this candidate author.

The parent must independently review and integrate the candidate, then obtain
a native result through the maintained serialized CI/build workflow. No
acceptance is inferred from this source review.
