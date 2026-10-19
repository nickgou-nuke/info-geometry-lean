# QMS Ground-Truth Contract — Section 145 TL/Kauffman Yang–Baxter

## Claim

For an associative unital ring `R` with a central `ℂ`-algebra structure, a
`TemperleyLiebSystem δ R` and elements `a b : ℂ`, put
`Bᵢ = a • 1 + b • eᵢ`. The TL quadratic and adjacent cubic relations imply

`B₁ B₂ B₁ - B₂ B₁ B₂ = (a^2*b + a*b^2*δ + b^3) • (e₁ - e₂)`.

Consequently the braid/Yang–Baxter relation holds if the displayed scalar
coefficient vanishes. In the Kauffman specialization `a*b = 1` and
`δ = -(a^2+b^2)`, the coefficient vanishes.

The theorem establishes only the local two-generator Artin relation. It does
not establish invertibility or distant-generator relations needed for a full
braid-group representation.

## Carrier and conventions

The carrier is the repository-owned `TemperleyLiebJonesBridge.TemperleyLiebSystem`
over `R`, with its explicit multiplication and `ℂ`-algebra scalar action.
No commutation assumption is made between `e₁` and `e₂`. Products are in the
written order. The parameters are central scalars from `ℂ`.

## Existing repository facts

- `lean/InfoGeometry/Canonical/TemperleyLiebJonesBridge.lean` defines
  `TemperleyLiebSystem` with `e1`, `e2`, both loop relations, and both cubic
  contractions.
- `lean/InfoGeometry/Topology/WittenJonesChernSimonsKnots.lean` contains a
  concrete noncommutative `Mat3` Kauffman braid equation under the inverse
  parameter hypothesis. Its coordinate proof does not establish the generic
  TL algebra theorem.
- The Witten–Jones owner separately states an octonionic framing-anomaly
  difference identity. No existing theorem was identified that maps that
  quantity to the generic TL braid representation.

## Minimal gap

Prove the algebraic difference identity in a reusable theorem and derive the
Kauffman specialization. Keep the implication scoped to explicit TL and scalar
parameter hypotheses.

## Excluded claims

This contract does not assert that a framing anomaly causes, necessitates, or
derives Yang–Baxter. That would require a separately constructed map from the
framing data to the TL representation and a proved compatibility theorem. It
also does not assert a topological Chern–Simons TQFT construction from these
finite algebraic relations alone.

## QMS status

Bucket 2 conditional algebraic theorem; risk R2. Section number is the user's
requested work label. Existing related Witten–Jones owner prose calls its
module Section 148; this work will not rename that owner.
