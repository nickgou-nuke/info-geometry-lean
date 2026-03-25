# Triality and Path-Hysteresis Note

This note replaces older speculative "D4 crystal" prose with a code-backed topic map.

## Current owner modules

The current triality / routing / hysteresis packet is spread across:
- `lean/InfoGeometry/Canonical/Triality.lean`
- `lean/InfoGeometry/Canonical/BregmanTriality.lean`
- `lean/InfoGeometry/Canonical/Attention.lean`
- `lean/InfoGeometry/Canonical/AttentionSplit.lean`
- `lean/InfoGeometry/Canonical/AttentionEuclidean.lean`
- `lean/InfoGeometry/Canonical/WeylPathHysteresis.lean`
- `lean/InfoGeometry/Canonical/HolographicEmergence.lean`

## What is actually represented

- triadic routing and metric-compatible attention live in the triality and attention files;
- order-sensitive update witnesses now live in `WeylPathHysteresis`, not in the old monolithic `WeylInformationGauge` shell;
- higher synthesis or interpretation should be treated as consumer-level prose, not as foundational ontology.

## How to read this topic today

If you want formal content, start from the owner modules above and ignore older claims that frame the entire packet as a single "crystal" theory. The current repo structure treats it as a combination of routing, transport, and path-dependence layers.
