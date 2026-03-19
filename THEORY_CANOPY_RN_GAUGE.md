# RN / Gauge Canopy

This document is the second top-level semantic map of the repository.

It complements [THEORY_CANOPY.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY.md).

The first canopy is centered on the currently verified KK/index bridge:

`KasparovCycle -> AnalyticalIndex -> GrandSynthesis`

This second canopy is centered on a different deep root system:

- Radon-Nikodym density
- relative volume change
- Kähler/RN potential
- Weyl gauge transport
- modular/RN continuum structure

The main claim of this map is:

> RN density, volume change, and gauge transport are not peripheral decoration.
> They form one of the deepest root systems of the theory.

## The Short Picture

The RN / gauge story currently reads like this:

`relativeCountDensity / relativeTomitaTakesakiOp`
-> `kahlerPotentialRN / relativeVolumeChangeRN`
-> `RNEntropySourcesMongeAmpere`
-> `DiracRicciBridge / ConformalUnification`
-> `WeylGaugeField / WeylTransport`
-> `GrandSynthesis`

This is not a single linear chain in the code. It is a braided root system whose
branches meet again in the synthesis layer.

## The RN / Gauge Layers

| Layer | Role | Main file(s) | Key hubs / concepts |
| --- | --- | --- | --- |
| Primitive RN density | finite-model RN/log-density seed | `lean/InfoGeometry/Canonical/GrandSynthesis.lean` | `relativeCountDensity`, `relativeLogDensityMean`, `relativeModularHamiltonian`, `relativeTomitaTakesakiOp`, `relativeCountDensity_eq_rn_lift` |
| RN volume / Kähler trunk | RN Jacobian, Kähler potential, relative volume factor | `lean/InfoGeometry/Canonical/GrandSynthesis.lean`, `lean/InfoGeometry/Canonical/DiracRicciBridge.lean` | `kahlerPotentialRN`, `relativeVolumeChangeRN`, `RNEntropySourcesMongeAmpere` |
| Gauge transport trunk | local Weyl field + scale-equivariant transport | `lean/InfoGeometry/Canonical/WeylGaugeField.lean`, `lean/InfoGeometry/Canonical/WeylTransport.lean` | `WeylGaugeField`, `WeylGaugeField.along`, `WeylGaugeField.respond`, `ScaleEquivariantFlow`, `connectionAlong`, `generatedAlong` |
| Modular continuum branch | continuum modular structure internalized from RN primitives | `lean/InfoGeometry/Canonical/YangMillsContinuum.lean` | `ModularRadonNikodymData` and its derived modular interface |
| Synthesis / closure layer | RN-volume and gauge information reappear in capstone closure theorems | `lean/InfoGeometry/Canonical/ConformalUnification.lean`, `lean/InfoGeometry/Canonical/GrandSynthesis.lean` | conformal collapse from `kahlerPotentialRN` and `relativeVolumeChangeRN`, Wheeler-DeWitt-facing synthesis |

## Why This Looks Foundational

There are three strong signals.

### 1. RN appears early, not late

In [GrandSynthesis.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/GrandSynthesis.lean), the first-quantization layer already starts from RN-style density data:

- `relativeCountDensity`
- `relativeModularHamiltonian`
- `relativeTomitaTakesakiOp`
- `relativeCountDensity_eq_rn_lift`

So RN density is not only a downstream interpretation. It appears as a primitive
encoding layer.

### 2. Volume change is treated as semantic structure, not a side calculation

The same file defines:

- `kahlerPotentialRN`
- `relativeVolumeChangeRN`
- `RNEntropySourcesMongeAmpere`

and then uses them to build geometric consequences.

In [DiracRicciBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DiracRicciBridge.lean), the RN side is explicitly tied to Ricci/metric consequences:

- `relativeVolumeChangeRN = exp (-kahlerPotentialRN)`
- negativity/log-volume identities
- vacuum-gravity style bridge statements from RN entropy sourcing plus unit volume

This is much closer to root geometry than to bookkeeping.

### 3. Gauge transport is not separate from the semantic spine

The gauge layer is not isolated from the canonical spine. In
[WeylGaugeField.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/WeylGaugeField.lean)
and [WeylTransport.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/WeylTransport.lean),
the RN/gauge side is already wired into the same `spine_functor` taxonomy used by
the DAG tooling:

- lifts
- constructors
- responders

That means the gauge branch is not just mathematically deep; it is also
structurally visible to the current automation machinery.

## Current Graph Evidence

Two trusted semantic exports already support this root map.

### `WeylTransport`

Trusted artifact:

- `reports/dag/WeylTransport.semantic-block.stdlib.json`

Current scale:

- `44` semantic block nodes
- `201` semantic edges
- `24` skeleton nodes

That is a large transport trunk, not a thin helper file.

### `GrandSynthesis`

Trusted artifact:

- `reports/dag/GrandSynthesis.semantic-block.stdlib.json`

Current scale:

- `56` semantic block nodes
- `90` semantic edges
- `30` skeleton nodes

And its key hubs already include RN-volume terms:

- `kahlerPotentialRN`
- `relativeVolumeChangeRN`

So the capstone crown itself confirms that RN volume structure is not marginal.

## The Deep Root Family

If you want the shortest RN/gauge reading route through the theory, use:

1. `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
   Start with `relativeCountDensity`, `relativeTomitaTakesakiOp`,
   `kahlerPotentialRN`, and `relativeVolumeChangeRN`.
2. `lean/InfoGeometry/Canonical/DiracRicciBridge.lean`
   Follow RN-volume change into Ricci/metric consequences.
3. `lean/InfoGeometry/Canonical/ConformalUnification.lean`
   See how RN Kähler potential and unit relative volume force conformal collapse.
4. `lean/InfoGeometry/Canonical/WeylGaugeField.lean`
   Move into local gauge structure on the canonical spine.
5. `lean/InfoGeometry/Canonical/WeylTransport.lean`
   See the heavy transport/integration layer over that gauge field.
6. `lean/InfoGeometry/Canonical/YangMillsContinuum.lean`
   Read the continuum modular interface extracted from RN primitives.

This is the best current deep-root route if your intuition is that
measure/RN/gauge structure is the real substrate.

## Relationship To The KK Canopy

The KK/index canopy and the RN/gauge canopy are not competing maps.

They capture two different vertical stories:

- KK/index canopy:
  the currently verified bridge discovered by `Skynet v2`
- RN/gauge canopy:
  the likely deeper geometric/modular substrate that feeds multiple higher
  branches

In practice:

- the KK canopy is better for current frontier-closing work
- the RN/gauge canopy is better for understanding the deeper geometric root
  system of the repository

## Related Entry Points

- [UNIVERSAL_VOLUME_STACK.md](/home/goutev/LEAN4/info-geometry-lean/UNIVERSAL_VOLUME_STACK.md)
- [THEORY_CANOPY.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY.md)
- [README.md](/home/goutev/LEAN4/info-geometry-lean/README.md)
- [NEWCOMER_PATH.md](/home/goutev/LEAN4/info-geometry-lean/NEWCOMER_PATH.md)
- [lean/DAG/README.md](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/README.md)
- [docs/auto/index.md](/home/goutev/LEAN4/info-geometry-lean/docs/auto/index.md)
