# Ground-truth contract: inner derivation on the Cl(1,1) tower limit

## Claim

For the repository-owned ring direct limit `Cl11TensorTowerLimit.Limit`, the
commutator with any fixed element is an additive Leibniz derivation. For a
finite-stage generator and observable, this limit derivation agrees exactly
with the image of the finite-stage commutator under `ofStage`.

## Carrier and conventions

The carrier is `InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit`, the direct
limit of `Stage n := Cl11TensorTower.MatStage n` under the actual ring maps
`stageBond`. The bracket convention is `[H, X] = H * X - X * H`. No norm,
completion, scalar coordinate model, commutativity, or flow parameter is part
of this contract.

## Existing owners and exact evidence

* `Cl11TensorTowerLimit.lean` defines `Stage`, `stageBond`, `Limit`, and the
  ring homomorphism `ofStage`.
* `OperatorAlgebra/LieJordanPeirceColimit.lean` owns the concrete Peirce and
  Lie--Jordan transport into this exact limit, including `ofStage_plus`,
  `ofStage_minus`, and `composition_defect_nonzero_iff`.
* `OperatorAlgebra/PeirceSpine/RingHomTransport.lean` proves that ring
  homomorphisms preserve the commutator and the Tetraktys generators.
* `Optics/OperatorDerivationForms.lean` provides normed continuous operator
  derivations and exponential flows, but the algebraic direct-limit ring is not
  asserted there to be a complete normed algebra.

## Smallest gap

The limit owner has not exposed the elementary inner-commutator product rule
on `Limit` and its compatibility with `ofStage`. Add these exact facts to the
existing owner rather than creating a parallel limit or claiming analytic
exponentiation on `Limit`.

## Explicit boundary

This proves an algebraic derivation on the direct-limit ring and finite-stage
readback. It does not identify the distinct `Cl(1,1)`, `Cl(2,2)`, and
`Cl(5,5)` towers, construct a common tower morphism, provide a topology or
completion on the limit, or prove a parameter-dependent Lie flow there.
