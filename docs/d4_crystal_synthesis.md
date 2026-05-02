# Triality And Path-Hysteresis Topic Map

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This is a topic map for the triality, routing, and path-hysteresis family.

It is not a synthesis theorem and it is not part of the current main closure
burden around the corrected phase-space trunk.

## Current files

The current packet is best read through:

- `lean/InfoGeometry/Canonical/Triality.lean`
- `lean/InfoGeometry/Canonical/BregmanTriality.lean`
- `lean/InfoGeometry/Canonical/Attention.lean`
- `lean/InfoGeometry/Canonical/AttentionSplit.lean`
- `lean/InfoGeometry/Canonical/AttentionEuclidean.lean`
- `lean/InfoGeometry/Canonical/WeylPathHysteresis.lean`
- `lean/InfoGeometry/Canonical/HolographicEmergence.lean`

## Current reading

The current code-backed reading is:

- triality and routing geometry live in the triality and attention files;
- order-sensitive or path-dependent update structure lives in
  `WeylPathHysteresis`;
- broader interpretation remains downstream consumer prose unless an explicit
  bridge theorem proves more.

## Relation to the main trunk

This topic family is adjacent to the main trunk, but not currently one of the
live closure junctions. It should therefore be read as a separate topic packet,
not as a hidden semantic root for the corrected phase-space, recomposition, or
KKT/conformal corridors.

## Use rule

If you want formal content, start from the files above and ignore older
high-level “crystal” language.
