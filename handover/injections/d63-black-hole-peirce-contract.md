# D63 Peirce horizon theorem contract

## Claim

In an associative unital ring `B` with an idempotent `P`, define the two
Peirce corners `N₊ = P A (1-P)` and `N₋ = (1-P) C P`, together with
`Q₊ = N₊N₋`, `Q₋ = N₋N₊`, `V = Q₊ + Q₋`, and `Σ = Q₊ - Q₋`. Prove the
following algebraic claims: cyclic traces identify the readouts of `Q₊` and
`Q₋`; adding diagonal Peirce components to `A,C` leaves `V,Σ` unchanged;
the existing logistic state has product with its complement `V - V²`;
two-cone mirror and sandwich identities hold; and the ordered product of
the two square-zero corner shears has an explicit two-sided inverse.

## Carrier and conventions

Carrier: `[Ring B]`, and `[StarRing B]` only where needed to import the
existing logistic owner. Multiplication is associative and not assumed
commutative. The trace is a functional `B → R` with explicitly stated
additivity, subtraction, zero, and cyclicity hypotheses. No positivity,
entropy, norm, topology, time evolution, or physical interpretation is part
of the theorem contract.

## Repository owners

- `InfoGeometry.OperatorAlgebra.PeirceSpine.Basic`: `conePlus`, `coneMinus`,
  `evenGrade`, `genPhi`, `genJ`, `genV`, `genSig`, and `peirce_nf`.
- `InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys`:
  `archetype_A3_nilpotent_cones_and_tetraktys_table`, including both cone
  square-zero laws and `genSig * genSig = genV * genV`.
- `InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceLogisticBitwordBridge`:
  `peirceLogistic_operator_identities`.
- Existing `InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotencyDefectMatrixD63`
  already owns the D63 filename in the Peirce spine; this task must not replace
  it.

## Smallest gap and causal dependencies

The requested black-hole-named packaging is absent from the inspected
PeirceSpine owner surface. The reusable operator identities are already
present. A new, separately named module may assemble them and prove only the
listed ring identities. The dependency graph is: Peirce cut → paired sheets;
paired sheets → logistic impurity and mirror sandwiches; Peirce cut → invertible
two-cone shear. Trace balance and diagonal-deformation invariance are direct
consequences of the paired Peirce corners.

## Explicitly unproved adjacent claims

These algebraic results do not establish Bekenstein–Hawking entropy or an area
law, a quantum Page curve, Hayden–Preskill decoding, evaporation, unitarity in
the star sense, or resolution of the black-hole information paradox. A
cyclic trace is not assumed positive and is not an entropy functional. A
two-sided inverse is not a unitary operator unless additional involution laws
are proved.
