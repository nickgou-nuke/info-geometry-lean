# Universal Volume Stack

This document is the shortest validated reading path for the repository's
Universal Volume / Radon-Nikodym stack.

It is not a philosophical note. It is a code map.

The core idea is:

> multiplicative volume change is converted into additive logarithmic /
> Radon-Nikodym potential, and that additive potential is then reused in the
> modular, entropy, and synthesis layers.

## The Short Stack

Read the stack in this order:

1. [UniversalVolume.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/UniversalVolume.lean)
2. [Base.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/Base.lean)
3. [LogPotential.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/LogPotential.lean)
4. [RadonNikodym.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/RadonNikodym.lean)
5. [ConnesCocycle.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/ConnesCocycle.lean)
6. [GrandSynthesis.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/GrandSynthesis.lean)
7. [DiracRicciBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DiracRicciBridge.lean)
8. [ConformalUnification.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ConformalUnification.lean)

That route gives the exact root-to-crown path.

## What Each Layer Does

### 1. Umbrella

[UniversalVolume.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/UniversalVolume.lean)
is the façade. It exports the main interfaces:

- `VolumeHom`
- `LogAbsVolume`
- `HasScalarRNBridge`
- `rn_chain_rule`
- `IsConnesCocycle`
- `cocycle_additive_potential`

If you only want the names and the stacking order, start here.

### 2. Multiplicative volume

[Base.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/Base.lean)
defines:

- `VolumeHom`

This is the multiplicative root. In the current implementation it is realized by
the determinant on linear automorphisms.

### 3. Additive logarithmic lift

[LogPotential.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/LogPotential.lean)
defines:

- `LogAbsVolume`
- `logAbsVolume_add`

This is the first key bridge:

`multiplicative determinant-like volume -> additive log potential`

### 4. Radon-Nikodym bridge

[RadonNikodym.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/RadonNikodym.lean)
defines:

- `HasScalarRNBridge`
- `HasScalarRNBridge.toExactBridge`
- `HasScalarRNBridge.toLogGenerator`
- `rn_eq_additiveInvariant`
- `rn_eq_logGenerator`
- `rn_chain_rule`

This file is the exact “volume change becomes additive RN potential” layer.

The most important shortcut theorem here is:

- [rn_chain_rule](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/RadonNikodym.lean)

### 5. Connes cocycle descent

[ConnesCocycle.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/ConnesCocycle.lean)
adds the modular/operator-algebraic layer:

- `AdditiveModularFlow`
- `IsConnesCocycle`
- `ScalarCocycleBridge`
- `scalarCocycle`
- `scalarCocycle_mul`
- `cocycleLogPotential`

This is where the stack stops being “just determinant algebra” and becomes a
modular dynamics interface.

### 6. Canonical RN synthesis points

In [GrandSynthesis.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/GrandSynthesis.lean),
the RN stack is internalized in the finite canonical model through:

- `relativeCountDensity`
- `relativeModularHamiltonian`
- `relativeTomitaTakesakiOp`
- `relativeCountDensity_eq_rn_lift`
- `kahlerPotentialRN`
- `relativeVolumeChangeRN`
- `RNEntropySourcesMongeAmpere`

This is the shortest route from the abstract volume stack to the theorem
library's synthesis surface.

### 7. Geometric and conformal consequences

[DiracRicciBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DiracRicciBridge.lean)
and [ConformalUnification.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ConformalUnification.lean)
show how the RN/Kähler layer feeds:

- relative volume identities
- Ricci/metric bridge consequences
- conformal collapse statements under unit-volume closure

## The Fastest Shortcuts

If you only want the shortest path, use one of these:

### Shortcut A: conceptual minimum

1. [UniversalVolume.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/UniversalVolume.lean)
2. [RadonNikodym.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/RadonNikodym.lean)
3. [ConnesCocycle.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/ConnesCocycle.lean)
4. [GrandSynthesis.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/GrandSynthesis.lean)

### Shortcut B: theorem-oriented minimum

1. [rn_chain_rule](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/RadonNikodym.lean)
2. `relativeCountDensity_eq_rn_lift` in [GrandSynthesis.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/GrandSynthesis.lean)
3. `kahlerPotentialRN` in [GrandSynthesis.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/GrandSynthesis.lean)
4. `relativeVolumeChangeRN` in [GrandSynthesis.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/GrandSynthesis.lean)
5. `RNEntropySourcesMongeAmpere` in [GrandSynthesis.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/GrandSynthesis.lean)

### Shortcut C: physics-facing minimum

1. [ConnesCocycle.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Volume/ConnesCocycle.lean)
2. [GrandSynthesis.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/GrandSynthesis.lean)
3. [DiracRicciBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DiracRicciBridge.lean)
4. [ConformalUnification.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ConformalUnification.lean)

## What Is Actually Verified

The following claims are directly supported by the current code:

- there is a multiplicative volume homomorphism layer
- there is an additive logarithmic potential layer
- there is a constructive scalar RN bridge with an additive chain rule
- there is a Connes-cocycle-style modular layer
- there is a canonical RN/Kähler/relative-volume layer in `GrandSynthesis`

This means the statement

`volume change -> logarithmic/RN potential -> modular/entropy structure`

is not interpretation imposed from outside. It is a real code path.

## Relationship To The Other Canopies

This stack is the most precise local guide for the volume/RN side.

Use:

- [THEORY_CANOPY.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY.md)
  for the current high-level KK/index crown map
- [THEORY_CANOPY_RN_GAUGE.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY_RN_GAUGE.md)
  for the broader RN/gauge root system
- this file
  for the exact Universal Volume stack itself

## Related Entry Points

- [README.md](/home/goutev/LEAN4/info-geometry-lean/README.md)
- [NEWCOMER_PATH.md](/home/goutev/LEAN4/info-geometry-lean/NEWCOMER_PATH.md)
- [THEORY_CANOPY.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY.md)
- [THEORY_CANOPY_RN_GAUGE.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY_RN_GAUGE.md)
