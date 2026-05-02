# Theorem-Candidate Doctrine: State-as-Functional, Basis-as-Map, Representation Bridge

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

Status: theorem-candidate doctrine note
Date: 2026-04-23
Scope: formal candidate doctrine for the operatorial trunk of `info-geometry-lean-fusion`

## Purpose

This note distills a recurring symbolic claim into a theorem-factory target:
- a state should be owned first as a positive normalized probe of an observable algebra;
- vector, density-matrix, doubled-real, Krein, BdG, Cartan, and Clifford presentations should appear as representation or transport surfaces;
- basis data should remain epistemological scaffolding rather than ontology.

This is not a proof note. It is a doctrine note that identifies the minimal truthful Lean targets and the remaining debt.

## Symbolic claim

The fertile but inflation-prone claim is:

```text
The algebra is the territory.
The state is the probe.
The basis is the map.
```

The theorem-factory reading is:
- the algebraic/observable lane should be primitive;
- a state should be modeled as a normalized functional/probe on that lane;
- representation-specific carriers (vector states, doubled real states, Krein states, BdG frames, Cartan frames) should be attached through explicit bridge structures or theorems;
- basis choices must not be confused with the ontology of statehood.

## Distilled invariant

The smallest truthful invariant to formalize now is:

1. define a minimal abstract state owner surface as a normalized linear probe on the observable carrier;
2. define a representation-frame surface whose only job is to expose coordinates on a chosen carrier;
3. define a bridge structure connecting the abstract probe to an existing doubled/Krein representation state;
4. prove that the bridge identifies the probe with representation expectation, while the frame remains additional structure rather than a constituent of the probe.

This is intentionally weaker than a full positive-functional / GNS / standard-form development.

## Repo corridor

### Existing owner/translator surfaces already present
- `lean/InfoGeometry/Canonical/StandardFormCore.lean`
  - `VectorState`
  - `VectorState.expectation`
  - `StandardFormSeed`
  - `StandardFormCarrier`
- `lean/InfoGeometry/Krein/State.lean`
  - projectivized Krein state space as a representation shadow
- `lean/InfoGeometry/Canonical/StateDependentTransport.lean`
  - state-indexed modular data/readouts on doubled real carrier
- `lean/InfoGeometry/Canonical/SouriauTomitaModularFlowBridge.lean`
  - operatorial Tomita/Souriau bridge with `SouriauTomitaKMSContext`
- `lean/InfoGeometry/Volume/ConnesCocycle.lean`
  - `AlgebraEnd`
  - additive modular flow owner lane

### Proposed new surface
- `lean/InfoGeometry/Canonical/AlgebraicStateFunctionalBridge.lean`

Role classification:
- owner: minimal abstract state-as-functional/probe structure
- translator: bridge from abstract probe to `StandardFormCore.VectorState`
- coherence: theorem that attached representation frame does not alter the probe identity

## What this note does NOT claim

This doctrine note does not claim:
- a full C*-algebra or von Neumann algebra formalization;
- a full positive-functional theory;
- a full GNS construction;
- a completed Type III / AQFT state theory;
- a proof that every abstract state already induces the doubled real/Krein representation desired by the larger symbolic story.

Those are future obligations.

## Minimal Lean target

The minimal Lean target should define:

- `PositiveNormalizedFunctional` or equivalently a normalized algebraic probe on `AlgebraEnd`;
- `RepresentationFrame` as coordinate scaffolding on a chosen representation carrier;
- `StateRepresentationBridge` connecting a probe to a `StandardFormCarrier` reference state;
- a theorem exposing `probe = expectation` under the bridge;
- a theorem or constructor showing that changing/attaching a frame does not change the probe identity.

## Why this target is honest

This target is honest because:
- the repo already owns `VectorState.expectation` on the doubled carrier;
- the repo does not yet own a full positive-functional / GNS theorem;
- therefore the smallest truthful move is to separate abstract probe from representation and connect them by explicit bridge data.

## Remaining debt

1. Strengthen `PositiveNormalizedFunctional` to a genuinely positive state notion once the repo has the right positivity surface.
2. Decide whether the eventual state owner should live over existing `AlgebraEnd` only or a more abstract observable-algebra interface.
3. Add a theorem-backed GNS-like bridge if and when the owner lane justifies it.
4. Add owner/translator surfaces for basis-as-map in stronger BdG/Majorana/Cartan corridors if needed.
5. Keep any Hestenes/STA/Type-III rhetoric as future-pass material until explicit bridge theorems exist.

## Recommended theorem names

Possible initial theorem surfaces:
- `PositiveNormalizedFunctional.probe_id`
- `PositiveNormalizedFunctional.ofNormalizedVectorState`
- `StateRepresentationBridge.probe_eq_referenceExpectation`
- `StateRepresentationBridge.probe_apply_eq_referenceExpectation`
- `StateRepresentationBridge.withFrame`
- `StateRepresentationBridge.withFrame_probe_eq`

## Doctrine law

```text
Statehood is owned first as probe.
Representation is attached second as bridge.
Basis enters third as map.
```

## Conclusion

The next truthful Lean move is not a full GNS implementation. It is a smaller owner/translator/coherence surface that lets the repo state, in code, that a state is first a normalized probe and only afterwards a represented vector/Krein object under explicit bridge data.
