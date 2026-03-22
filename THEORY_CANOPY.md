# Theory Canopy

This document is a compact semantic map of the repository's highest theory
layers.

It answers one question:

> If I look at the codebase from the top, what are the main crown, trunk, and
> root structures of the theory?

This canopy is a top view, not the whole story of primitiveness. The repository
should be read as a DAG with a root set, not as a single-spine tree. The canopy
shows the visible trunks and crowns. The true axiomatic base sits deeper than
some of those trunks.

## The Short Picture

The canopy is no longer single-spined. The current verified top-level story has
several real trunks:

1. primitive real split-Krein trunk:
   `KreinGradedModule`
   -> `RealSplitCl11Action`
   -> `RealSplitKreinKasparovCycle`
   -> `RealSplitKreinUnboundedCycle`
2. KK / analytical-index / synthesis:
   `InfoGeometry.KK.KasparovCycle.analyticalIndex`
   -> `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
   -> `InfoGeometry.Canonical.GrandSynthesis.*`
3. source-tension / Rosetta / modular anomaly:
   `Singular`, `RicciMongeAmpere`, `BogoliubovFockSuper`, `TomitaTakesaki`
   -> `InfoGeometry.Canonical.Rosetta.*`
   -> `InfoGeometry.Quantum.ModularAnomaly.*`
4. discrete Hurwitz shell / RG stationarity:
   `InfoGeometry.Quantum.Hurwitz`
   -> `InfoGeometry.Quantum.HurwitzRGFlow`
   -> `InfoGeometry.Canonical.RGFlow`
5. finite Pfaffian-sign phase boundary:
   `InfoGeometry.Quantum.KitaevChain.index_change_forces_defect_crossing`

The older KK/index route remains the cleanest classical-style vertical bridge,
but it is no longer the only crown-facing corridor worth showing newcomers.

## The Root Set Beneath The Canopy

The deepest base currently visible in the repo is not one file and not one
seed. It is a root set built from at least two families.

1. count / ray / RN base
- unnormalized counts, relative densities, RN lifts, relative volume change,
  modular/RN operators, and gauge transport data
2. real split-Krein operator base
- `KreinGradedModule`, real Krein carriers, endomorphism language,
  `RealSplitCl11Action`, and the derived internal axis `K := J.comp eps`

Normalized probability, entropy, KL, IB, analytical index, and synthesis live
above those floors.

## The Canopy Layers

| Layer | Role | Main file(s) | Key hubs |
| --- | --- | --- | --- |
| Umbrella / Publication Surface | stable top-level façades | `lean/InfoGeometry/All.lean`, `lean/InfoGeometry.lean`, `lean/InfoGeometry/Library.lean`, `lean/InfoGeometry/Canonical/All.lean` | import/publication surface, not the deepest semantic hubs |
| Crown / Capstone Synthesis | highest synthesis surfaces currently visible | `lean/InfoGeometry/Canonical/GrandSynthesis.lean`, `lean/InfoGeometry/Canonical/Rosetta.lean`, `lean/InfoGeometry/Canonical/GrandSynthesisDoubleCopy.lean` | `information_wheeler_dewitt_equivalence_of_fullCapstone`, `rosetta_source_tension_three_presentations`, `modularCPT_source_rosetta` |
| Trunk / Bridge Layer | large vertical transport between roots and capstones | `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`, `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean`, `lean/InfoGeometry/Canonical/DoubleCopyUnification.lean` | `analyticalIndex`, `indexInvariantAlong_of_conjugacy`, `double_copy_geometric_equilibrium_imp` |
| Primitive Split-Krein Branch | current canonical real operator spine | `lean/InfoGeometry/Quantum/RealSplitClifford.lean`, `lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean`, `lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean` | `RealSplitCl11Action`, `RealSplitKreinKasparovCycle`, `RealSplitKreinUnboundedCycle` |
| Quantum / Modular Branch | real-Majorana, modular, and finite topological shadow layer | `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`, `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`, `lean/InfoGeometry/Quantum/ModularAnomaly.lean`, `lean/InfoGeometry/Quantum/KitaevChain.lean` | `unified_anomaly_bridge`, `thermal_berezinian_index`, `index_change_forces_defect_crossing` |
| Discrete / RG Branch | finite shell symmetry feeding RG fixed-point scaffolds | `lean/InfoGeometry/Quantum/Hurwitz.lean`, `lean/InfoGeometry/Quantum/HurwitzRGFlow.lean`, `lean/InfoGeometry/Canonical/RGFlow.lean` | `HurwitzShellAction.InvariantAtScale`, `betaFunction_eq_zero_of_invariantAtScale`, `existsUnique_fixedPoint_of_contracting` |
| Deep Count / RN / Gauge Root Family | the lower measure-theoretic and volume-change substrate | `lean/InfoGeometry/Canonical/GrandSynthesis.lean`, `lean/InfoGeometry/Canonical/WeylGaugeField.lean`, `lean/InfoGeometry/Canonical/WeylTransport.lean`, `lean/InfoGeometry/Canonical/YangMillsContinuum.lean` | `relativeCountDensity`, `relativeTomitaTakesakiOp`, `relativeVolumeChangeRN`, `ModularRadonNikodymData` |
| Root-Set Surfaces | compact roots from which visible trunks grow | `lean/InfoGeometry/Krein/Clifford.lean`, `lean/InfoGeometry/Quantum/RealSplitClifford.lean`, `lean/InfoGeometry/Canonical/GrandSynthesis.lean` | `KreinGradedModule`, `RealSplitCl11Action`, count/RN seed objects |

## What Is “Top” In Practice

There are two different meanings of top in this repository.

### 1. Import/publication top

The highest build-safe umbrella is:

- `lean/InfoGeometry/All.lean`

The main stable canonical publication surface is:

- `lean/InfoGeometry/Canonical/All.lean`

These files are important, but they are façades. They tell you what is exposed,
not necessarily where the deepest semantic bottlenecks live.

### 2. Semantic/DAG top

The crown is now distributed across several large consumer-side surfaces:

- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- `lean/InfoGeometry/Canonical/Rosetta.lean`
- `lean/InfoGeometry/Quantum/ModularAnomaly.lean`
- `lean/InfoGeometry/Canonical/GrandSynthesisDoubleCopy.lean`

Those are the files where multiple lower branches are named, transported, or
packaged into larger semantic stories.

### 3. Absolute depth from true roots

This is different again.

- seed distance in a Skynet packet is local to the chosen seed set
- absolute DAG depth is measured from the graph's true dependency roots
- a DAG usually has many primitive roots, not one common starting node

So the canopy is a useful top view, but it is not by itself the metric of true
axiomatic depth.

## Current Branch Families

### Primitive split-Krein branch

- `lean/InfoGeometry/Quantum/RealSplitClifford.lean`
- `lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean`
- `lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean`
- `lean/InfoGeometry/KK/RealSplitKreinCompactOperator.lean`

This is the current canonical real split operator spine.

### KK / index branch

- `lean/InfoGeometry/KK/KasparovCycle.lean`
- `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`

This remains the cleanest currently verified classical-style vertical route.

### Rosetta / Weyl / modular branch

- `lean/InfoGeometry/Canonical/Rosetta.lean`
- `lean/InfoGeometry/Quantum/ModularAnomaly.lean`
- `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
- `lean/InfoGeometry/Canonical/WeylTransport.lean`

This is a genuine transport corridor, not just a naming shell.

### Count / RN / gauge branch

- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- `lean/InfoGeometry/Canonical/DiracRicciBridge.lean`
- `lean/InfoGeometry/Canonical/WeylGaugeField.lean`
- `lean/InfoGeometry/Canonical/WeylTransport.lean`
- `lean/InfoGeometry/Canonical/YangMillsContinuum.lean`

This branch captures one of the deepest lower substrates of the theory.

### Discrete / RG / phase branch

- `lean/InfoGeometry/Quantum/Hurwitz.lean`
- `lean/InfoGeometry/Quantum/HurwitzRGFlow.lean`
- `lean/InfoGeometry/Canonical/RGFlow.lean`
- `lean/InfoGeometry/Quantum/KitaevChain.lean`

This branch captures discrete shell symmetry, RG stationarity, and finite
Pfaffian-sign phase boundaries.

## How To Read The Canopy

If you want the shortest meaningful routes through the theory, choose one of
these entry paths.

### Route A: true axiomatic-base route

1. `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
   Start with `relativeCountDensity`, `relativeTomitaTakesakiOp`,
   `kahlerPotentialRN`, and `relativeVolumeChangeRN`.
2. `lean/InfoGeometry/Krein/Clifford.lean`
   Read `KreinGradedModule` and the grading machinery.
3. `lean/InfoGeometry/Quantum/RealSplitClifford.lean`
   Read `RealSplitCl11Action` and the derived axis `K := J.comp eps`.
4. `lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean`
   Read the primitive bounded real split-Krein cycle.
5. `lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean`
   Read the primitive domain-based unbounded split-Krein scaffold.

### Route B: KK / synthesis trunk

1. `lean/InfoGeometry/Canonical/GeneratedFlow.lean`
2. `lean/InfoGeometry/KK/KasparovCycle.lean`
3. `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
4. `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean`
5. `lean/InfoGeometry/Canonical/GrandSynthesis.lean`

### Route C: modular / CPT / Rosetta trunk

1. `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean`
2. `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`
3. `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
4. `lean/InfoGeometry/Quantum/ModularAnomaly.lean`
5. `lean/InfoGeometry/Canonical/Rosetta.lean`

### Route D: discrete shell / RG / phase trunk

1. `lean/InfoGeometry/Quantum/Hurwitz.lean`
2. `lean/InfoGeometry/Quantum/HurwitzRGFlow.lean`
3. `lean/InfoGeometry/Canonical/RGFlow.lean`
4. `lean/InfoGeometry/Quantum/KitaevChain.lean`

## How This Map Is Produced

This file is informed by:

- trusted semantic block exports
- Skynet v2 frontier packets
- the current generated status page at `docs/auto/index.md`
- the current theorem surface in the synchronized capstone modules

It is therefore a curated semantic map, not a raw import listing.

## A Second Deep Root Map

This canopy is centered on the currently visible high-level trunks.

There is also a second, deeper root-centered map focused on:

- unnormalized counts and rays
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
- `UNIFICATION_INDEX.md`
- `lean/DAG/README.md`
- `docs/auto/index.md`
- `SELF_OPTIMIZATION_PROTOCOL.md`
