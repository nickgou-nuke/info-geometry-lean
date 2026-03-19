# Theory Canopy

This document is a compact semantic map of the repository's highest theory
layers.

It answers one question:

> If I look at the codebase from the top, what are the main crown, trunk, and
> root structures of the theory?

The repository is best understood as a **layered DAG**, not as a strict binary
tree. Dense semantic hubs live below, while stable umbrella modules expose
cleaner publication surfaces above.

## The Short Picture

The current verified vertical story is:

`InfoGeometry.KK.KasparovCycle.analyticalIndex`
-> `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
-> `InfoGeometry.Canonical.GrandSynthesis.*`

That is the most important currently verified trunk-to-crown bridge in the
repository.

## The Canopy Layers

| Layer | Role | Main file(s) | Key hubs |
| --- | --- | --- | --- |
| Umbrella / Publication Surface | stable top-level façades | `lean/InfoGeometry/All.lean`, `lean/InfoGeometry.lean`, `lean/InfoGeometry/Library.lean`, `lean/InfoGeometry/Canonical/All.lean` | import/publication surface, not the deepest semantic hubs |
| Crown / Capstone Synthesis | highest semantic synthesis currently visible | `lean/InfoGeometry/Canonical/GrandSynthesis.lean` | `bochnerWeitzenboeckBridge_of_ibDynamics`, `kahlerPotentialRN`, `information_wheeler_dewitt_implication_of_ibDynamics_and_indexHypotheses`, `relativeVolumeChangeRN`, `AlgebraicEquilibriumCl11` |
| Trunk / Bridge Layer | large vertical transport between foundational and capstone layers | `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`, `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean` | `analyticalIndex`, `chiralProjectorPlus`, `chiralProjectorMinus`, `chiralKernelSliceMinus`, `chiralKernelSlicePlus`, `IsCStarLayer`, `IsCompleteCStarLayer` |
| Seed / Root | compact KK-theoretic seed from which the verified bridge grows | `lean/InfoGeometry/KK/KasparovCycle.lean` | `EndH`, `IsCompactEnd`, `KasparovCycle`, `KasparovCycle.analyticalIndex` |

## What Is “Top” In Practice

There are two different meanings of “top” in this repository.

### 1. Import/publication top

The highest build-safe umbrella is:

- `lean/InfoGeometry/All.lean`

The main stable canonical publication surface is:

- `lean/InfoGeometry/Canonical/All.lean`

These files are important, but they are façades. They tell you what is exposed,
not necessarily where the deepest semantic bottlenecks live.

### 2. Semantic/DAG top

The top semantic crown currently visible in trusted graph exports is:

- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`

This is where the currently discovered highest consumer-side capstones live,
including:

- `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_equivalence_of_state_capstone_hypotheses`
- `InfoGeometry.Canonical.GrandSynthesis.information_wheeler_dewitt_equivalence_of_fullCapstone`

## Current Branch Families

The current trusted view suggests these main branch families:

### KK / index branch

- `lean/InfoGeometry/KK/KasparovCycle.lean`
- `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`

This is the cleanest currently verified vertical route.

### Operator-algebra branch

- `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean`

This is thinner than `AnalyticalIndex`, but it is a real vertical operator layer.

### Synthesis branch

- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`

This is the current semantic crown.

### Transport / gauge branch

- `lean/InfoGeometry/Canonical/GeneratedFlow.lean`
- `lean/InfoGeometry/Canonical/WeylGaugeField.lean`
- `lean/InfoGeometry/Canonical/WeylTransport.lean`

This is another major branch family, but the presently verified KK bridge is not
centered there; it is centered through `AnalyticalIndex`.

## How To Read The Canopy

If you want the shortest meaningful route through the theory, use:

1. `lean/InfoGeometry/Canonical/GeneratedFlow.lean`
2. `lean/InfoGeometry/KK/KasparovCycle.lean`
3. `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
4. `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean`
5. `lean/InfoGeometry/Canonical/GrandSynthesis.lean`

This is not the only reading order, but it is currently the most useful
root-to-crown route supported by trusted semantic graph evidence.

## How This Map Is Produced

This file is informed by:

- trusted semantic block exports
- Skynet v2 frontier packets
- the current generated status page at `docs/auto/index.md`

It is therefore a **curated semantic map**, not a raw import listing.

## A Second Deep Root Map

This canopy is centered on the currently verified KK/index bridge.

There is also a second, deeper root-centered map focused on:

- Radon-Nikodym density
- relative volume change
- Kähler/RN potential
- Weyl gauge transport
- modular RN data

For that route, read [THEORY_CANOPY_RN_GAUGE.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY_RN_GAUGE.md).

## Related Entry Points

- `THEORY_CANOPY_RN_GAUGE.md`
- `README.md`
- `NEWCOMER_PATH.md`
- `lean/DAG/README.md`
- `docs/auto/index.md`
- `SELF_OPTIMIZATION_PROTOCOL.md`
