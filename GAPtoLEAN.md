# GAP-to-Lean Translation Contract

This document is the carrier-synchronization contract for the concrete
`G₂(2)` formalization. GAP, CHEVIE, and symbolic systems derive and audit
finite data. Lean/mathlib source is the proof authority: a CAS result is not
a Lean theorem until the translated statement is kernel-checked.

## Authoritative carrier

The GAP matrices must be exported from the Lean carrier in this coordinate
order:

```text
(a, b, x0, x1, x2, y0, y1, y2)
```

The relevant owners are `G2TwoMatrixCarrier.lean`,
`G2LeanCarrierMatrixAlignment.lean`, and `G2CASGeneratorAlignment.lean`.
Do not use `SylowSubgroup`, `Pcgs`, an arbitrary PC isomorphism, or an
unrelated Atlas representation as the source of a Lean theorem. The fixed
carrier exporter is `scripts/export_carrier_pc_rows.g`.

## Indices and words

Lean uses zero-based `Fin n`; GAP uses one-based list and permutation indices:

```text
Lean i  <->  GAP i + 1
GAP j   <->  Lean j - 1
```

GAP `ExtRepOfObj(Factorization(...))` is a list of signed pairs
`[generator, exponent, ...]`. Translate each pair to
`((generator - 1 : Nat) : Fin 8, exponent : Int)`. The exponent stays an
`Int`; it must not be silently changed to `Nat` or `Bool`. The canonical Lean
evaluator is `G2FlagWordEvaluator.lean`.

The generator order is:

```text
1..6 = pcGenerator 0..5
7    = swap01Aut
8    = correctedT
```

## Matrix orientation

Lean uses column vectors and `Matrix.mulVec`. The `j`-th matrix column is the
image of `basis8 j`:

```lean
autMatrix f i j = carrierToVec (f (basis8 j)) i
```

The native round-trip owners are `autMatrix_vec_action`, `autMatrix_action`,
and `autMatrix_injective` in `G2TwoMatrixCarrier.lean`.

## Contravariant multiplication

The essential law is:

```lean
autMatrix (f * g) = autMatrix g * autMatrix f
```

Thus the Lean word `f₁ * f₂ * ... * fₙ` has matrix word
`M(fₙ) * ... * M(f₂) * M(f₁)`. Every CAS factorization must pass both:

1. GAP matrix evaluation equals the exported matrix.
2. Lean `autMatrix` evaluation equals the same matrix.

Only then may `autMatrix_injective` prove the Lean equality.

## GAP matrix construction

For a column-coded Lean matrix, use:

```gap
List([1..8], i ->
  List([1..8], j ->
    ((Int(c[j] / 2^(i-1)) mod 2) * One(GF(2)))));
```

The bit position and matrix entry order must not be transposed. Existing
native alignment lemmas are:

```lean
autMatrix_pcGenerator_eq_casPCMatrix
autMatrix_swap01Aut_eq
autMatrix_correctedT_eq
```

## Coset variance

Lean `QuotientGroup` uses the relation `g⁻¹ * h ∈ B`. For quotient transport
use GAP `LeftCosets(G,B)` with explicit left translation. `RightCosets(G,B)`
with `OnRight` is a different action convention and cannot be identified
with the Lean quotient without a proved variance conversion.

The native double-coset interface is in `G2BNPair.lean`. A quotient equality
must eventually be reduced in Lean to:

```lean
change g⁻¹ * h ∈ B
```

## CAS gates before Lean promotion

The carrier-specific CAS audit must pass the applicable checks for fixed
carrier size, generator matrix alignment, PC relations, generated group
order, Weyl involutions and Coxeter order, parabolic orders, flag orbit
partition, the 12-cell partition, and full double-coset coverage.

The maintained concrete audit is `scripts/verify_g2_true_bruhat_cover.g`.
Its current verified output includes:

```text
LEAN_API_GENERATED_GROUP_ORDER=12096
LEAN_API_T_ORDERS=2, product=6
LEAN_API_BRUHAT_COVER=PASS
LEAN_CORRECTED_BRUHAT_COVER=PASS
EXACT_FLAG_ORBIT_PARTITIONS=PASS
TRUE_BRUHAT_COVER=PASS
```

`scripts/verify_g2_flag_cells_alignment.py` checks the frozen 189-cell table;
that script is evidence, not a Lean proof.

## Native quotient target

The remaining native construction is:

```lean
Fin 189 ≃
  SplitOctF2Aut ⧸
    G2TwoPCSubgroupClosure.unipotentSubgroup
```

It must be constructed from the CAS `FLAG_REP_EXT` words and proved in Lean.
The exact obligations are:

1. correct Lean evaluation of every representative word;
2. quotient equality via `g⁻¹ * h ∈ B`;
3. injectivity of the 189 representative cosets;
4. surjectivity onto the quotient;
5. transport of the 12 certified orbit cells;
6. `concreteBruhatCovering = Set.univ`;
7. `Subgroup.closure ... = ⊤`.

No relabeling, incidence table, opaque certificate, conditional axiom, or
proxy proposition may replace these obligations.

## Promotion order

```text
Lean carrier export
  -> GAP/CHEVIE computation on that exact carrier
  -> independent CAS PASS report
  -> explicit translated data
  -> native Lean equality lemmas
  -> quotient and structural theorems
```

The authority order is Lean owner source, then `lake env lean` or a locked
Lake build, then CAS audit artifacts, then documentation and generated
reports.

