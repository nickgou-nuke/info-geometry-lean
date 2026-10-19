# Ground-Truth Theorem Contract: Double Real Krein Projector Pairing

## Claim

For the repository's canonical carrier `DoubledSpace E = WithLp 2 (E × E)`, with
`E` a real complete inner-product space and with the existing epsilon spectral
projectors `spectralPlusProj` and `spectralMinusProj`, the indefinite pairing
`KreinSpace.kreinInner` equals the positive Hilbert pairing on the positive
projector image minus the positive Hilbert pairing on the negative projector
image:

```lean
KreinSpace.kreinInner u v =
  inner ℝ (spectralPlusProj u) (spectralPlusProj v) -
    inner ℝ (spectralMinusProj u) (spectralMinusProj v)
```

## Carrier and conventions

- Carrier: `DoubledSpace E := WithLp 2 (E × E)` from `Krein/DoubledSpace.lean`.
- The native Krein fundamental symmetry on `KreinSpace` is `spectral_epsilon`,
  the coordinate sign flip; `kreinInner u v = ⟪spectral_epsilon u, v⟫`.
- The projectors are the existing epsilon eigenspace projectors from
  `Clifford/Grading.lean`, re-exported through `Krein/PolarizedSector.lean`.
- `doubledCarrier` is a separate `InvolutiveSelfDualCarrier`: its `J` is the
  coordinate swap and its `kreinPairing` is the positive Hilbert sum. This
  theorem does not identify that pairing with `KreinSpace.kreinInner`.

## Existing declarations

- `Krein/KreinSpace.lean`: `kreinInner` is defined by the fundamental symmetry;
  `krein_inner_prod_l2` proves the coordinate formula
  `inner fst u fst v - inner snd u snd v`.
- `Krein/PolarizedSector.lean`: `spectralPlusProj_apply_eq_plusPoint` and
  `spectralMinusProj_apply_eq_minusPoint` identify projector outputs with the
  positive and negative coordinate embeddings.
- `Krein/SplitQuadraticSheets.lean`: `kreinInner_plusPoint` and
  `kreinInner_minusPoint` calculate the pairing on each sheet.
- `Clifford/Grading.lean`: spectral projectors and their algebraic laws.

These source declarations are proved in the checked-out owners; the proposed
bridge must be independently kernel checked.

## Minimal missing delta

Expose the indefinite pairing as the difference of the Hilbert pairings of
the existing positive and negative spectral projector components, using the
canonical real doubled carrier.

## Adjacent claims not established

This formula alone does not prove a colimit-level theorem, a Stokes or analytic
boundary theorem, finite signature indices, physical causal semantics, or an
identification of the positive `doubledCarrier.kreinPairing` with the
indefinite `KreinSpace.kreinInner`.
