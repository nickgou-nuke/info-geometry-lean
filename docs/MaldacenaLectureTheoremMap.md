# Maldacena Lecture Theorem Map

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Repo-native theorem-target map extracted from the Perimeter lecture on spacetime, black holes, wormholes, and entanglement.
> See: [README.md](../README.md), [docs/OperationalIntent.md](OperationalIntent.md), [docs/GenerativeDiscoveryArchitecture.md](GenerativeDiscoveryArchitecture.md), [FORMALIZATION_PROTOCOL.md](../FORMALIZATION_PROTOCOL.md)

This file turns the lecture themes into a concrete formalization program for this repository.

It does not claim that the repo already formalizes quantum gravity, Hawking radiation, or full AdS/CFT.
It identifies the parts of the lecture that can be translated honestly into current owner surfaces.

## Core Rule

Formalize the lecture in layers:

1. projective and modular geometry
2. entropy and thermodynamic closure
3. cocycle and invariant-readout structure
4. finite or toy entanglement/coarse-graining shadows
5. only then stronger holography language

Do not invert this order.

## What We Can Formalize Now

### 1. Projective / modular temperature geometry

These are live owner surfaces:

- [lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean](../lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean)
- [lean/InfoGeometry/Thermodynamics/SouriauModularS.lean](../lean/InfoGeometry/Thermodynamics/SouriauModularS.lean)
- [lean/InfoGeometry/Thermodynamics/ProjectiveTemperature.lean](../lean/InfoGeometry/Thermodynamics/ProjectiveTemperature.lean)
- [lean/InfoGeometry/Canonical/Algebraic/ModularRotorCocycle.lean](../lean/InfoGeometry/Canonical/Algebraic/ModularRotorCocycle.lean)

Concrete theorem targets:

- modular `S` as a named `SL2R` lift
- `S² = -I` through the explicit central lift `negIdSL2R`
- fixed-point theorems for `i` or `β = 1`
- closure involutions induced by projective inversion
- cocycle laws for modular action on geometric carriers
- stabilizer collapse from cocycle to strict homomorphism

### 2. Entropy / Gibbs / KMS / modular flow

These are already strong owner surfaces:

- [lean/InfoGeometry/Core/Entropy.lean](../lean/InfoGeometry/Core/Entropy.lean)
- [lean/InfoGeometry/Thermo/Gibbs.lean](../lean/InfoGeometry/Thermo/Gibbs.lean)
- [lean/InfoGeometry/Thermo/FiniteDiagonal.lean](../lean/InfoGeometry/Thermo/FiniteDiagonal.lean)
- [lean/InfoGeometry/Krein/Thermal.lean](../lean/InfoGeometry/Krein/Thermal.lean)
- [lean/InfoGeometry/Volume/ConnesCocycle.lean](../lean/InfoGeometry/Volume/ConnesCocycle.lean)

Concrete theorem targets:

- free-energy / entropy identities
- finite KMS-like invariance laws
- additive-time modular flow laws
- cocycle composition
- relative modular transport and log-generator statements

### 3. Projective state and gauge structure

These support the lecture’s “probability is not primary” reading:

- [lean/InfoGeometry/Core/ProjectiveSimplex.lean](../lean/InfoGeometry/Core/ProjectiveSimplex.lean)
- [lean/InfoGeometry/MeasureProjective.lean](../lean/InfoGeometry/MeasureProjective.lean)

Concrete theorem targets:

- normalized distributions as gauge-fixed representatives of rays
- projective logarithmic generators
- additive-constant gauge laws
- projective relative entropy shadows

## What We Should Build Next

### First corridor: modular closure and invariant readouts

This is the current implementation corridor.

Goal:
- make the projective-temperature sidecars rich enough that downstream files can state
  “this geometric/thermal point is fixed by the closure”
  and
  “all invariant readouts agree at that fixed point”

Why this corridor first:
- it is already repo-native
- it is mathematically honest
- it captures a real piece of the lecture’s inversion / fixed-point / closure story
- it avoids fake claims about black-hole dynamics

Current owner files:

- [lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean](../lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean)
- [lean/InfoGeometry/Thermodynamics/SouriauModularS.lean](../lean/InfoGeometry/Thermodynamics/SouriauModularS.lean)

### Second corridor: finite coarse-graining and subregion ignorance

This should be phrased as a finite or toy information-theoretic shadow, not as a full holographic theorem.

Suggested owner surfaces:

- extend [lean/InfoGeometry/Core/Entropy.lean](../lean/InfoGeometry/Core/Entropy.lean)
- add a finite “restricted readout / ignored region” toy module under `Core/` or `Thermo/`

Concrete theorem targets:

- ignoring part of a finite carrier increases coarse-grained uncertainty
- invariant readouts survive closure while local descriptions become mixed
- joint vs marginal readout distinctions

This is the right place to formalize the lecture’s “portion of the sentence” analogy in a mathematically honest finite model.

### Third corridor: paired carriers and entanglement shadows

This should not be called ER=EPR in Lean.

It should instead formalize:

- paired carriers with correlated readouts
- local mixedness with global coherence
- shared closure or cocycle data
- fixedness or invariance on the paired system

This gives a theorem-backed toy shadow of the lecture’s wormhole/entanglement discussion.

## What Is Too Early

Do not claim the repo currently formalizes:

- full Einstein equations as quantum emergence
- Hawking radiation
- black-hole evaporation unitarity
- actual wormhole traversability in physical spacetime
- full AdS/CFT
- rigorous black-hole area law in the gravitational sense

If such language appears in docs or packets, it must be labeled as heuristic, theory-formation, or toy-model intention unless backed by explicit Lean owners.

## Immediate Implementation Steps

1. strengthen the projective lift closure API
2. add fixed-point and readout theorems for the modular `S` anchor
3. define one finite coarse-graining toy surface
4. prove one entropy or readout monotonicity statement there
5. only then propose a boundary/bulk toy correspondence packet

## Current Status

The first corridor is active now.

Recent local implementation already provides:

- explicit central lift `negIdSL2R`
- `ProjectiveLiftTemperatureInversion`
- concrete modular `S` lift
- unit imaginary fixed-point witness
- closure-level fixedness theorem

The next mathematically clean extension is the finite coarse-graining / subregion-ignorance toy lane.
