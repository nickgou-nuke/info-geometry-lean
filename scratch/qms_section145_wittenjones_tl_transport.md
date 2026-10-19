# QMS Ground-Truth Contract — Witten–Jones TL Transport

## Claim

Specialize the existing custom Witten–Jones `Mat3` carrier to complex entries.
Construct an explicit equivalence with Mathlib's `Matrix (Fin 3) (Fin 3) ℂ`,
prove it preserves the operations used by the Kauffman operators, transport the
existing TL generator relations to a `TemperleyLiebSystem`, and derive the
concrete `121 = 212` equation from the generic Section 145 theorem.

## Carrier and conventions

The source carrier is `InfoGeometry.Topology.WittenJonesKnots.Mat3 ℂ` with its
repo-defined operations. The target is standard Mathlib matrices. The map is
an explicit carrier equivalence; no `Ring` or `Algebra` instance is added to
the bespoke carrier. The abstract TL theorem is applied only on the standard
matrix ring.

## Existing repo facts

- `Topology/WittenJonesChernSimonsKnots.lean` defines custom `Mat3`, its
  operations, TL generators and relations, Kauffman operators, and a concrete
  coordinate proof of YBE.
- `Canonical/TemperleyLiebJonesBridge.lean` owns the abstract
  `TemperleyLiebSystem`.
- `Canonical/TemperleyLiebKauffmanYangBaxter.lean` proves the generic TL
  defect identity and reciprocal Kauffman specialization.
- The framing-anomaly theorem remains a separate split-octonion identity; this
  contract does not connect it causally to YBE.

## Minimal gap

Prove operation preservation for the explicit map, construct the standard
matrix TL system, and transfer the generic theorem back to the existing custom
carrier. Keep the theorem finite and coefficient-specific to `ℂ`.

## Excluded claims

No full braid-group representation, Chern–Simons TQFT reconstruction,
framing-anomaly implication, or topological necessity theorem is asserted.
The existing owner is labeled Section 148; this work is an added bridge for
the user's Section 145 plan and does not rename the owner.

## QMS status

Bucket 2 conditional finite algebraic bridge; risk R3 because it adds a module
to the root import surface.

## Follow-up theorem contract: exact nondegenerate parameter criterion

### Claim

For the transported Witten–Jones matrix TL system over `ℂ`, with
`δ = -(a^2 + b^2)`, prove that the concrete local Yang–Baxter equation is
equivalent to `a * b = 1`, assuming `b ≠ 0` and `a^2 + b^2 ≠ 0`.

### Proof route

Use the generic exact defect identity. In this coefficient convention its
scalar factor is

```text
b * (a^2 + b^2) * (1 - a*b).
```

The concrete transported generators satisfy `e1 ≠ e2`, witnessed by an
explicit matrix entry. Read that entry from a zero defect to infer that the
scalar factor vanishes, then use the two nonzero assumptions to infer
`a*b = 1`. The converse is the existing reciprocal-parameter theorem.

### Excluded claims

This theorem characterizes the reciprocal normalization within the stated
nondegenerate finite matrix model. It does not derive that normalization from
the split-octonion phase-difference identity, and it does not establish a
topological framing-anomaly implication.
