---
title: Bohm–Madelung in Hestenes Operatorial Form (Doubled Krein)
status: draft
last_updated: 2026-04-08
---

# Bohm–Madelung in Hestenes Operatorial Form (Doubled Krein)

This note records the current operator-first formulation of a Bohm–Madelung-style
decomposition inside the doubled real Krein carrier. The guiding rule is that
no scalar diagonal proxies are introduced; all primitives are operatorial and
the complex unit is geometrized via the Hestenes axis `K = J ∘ ε`.

## 1. Primitive Ontology (No Background Spacetime)

The primitive objects are:

- projective state rays on the doubled carrier `H₂`,
- operator seeds `A : EndH`,
- modular transport generators,
- QGT readouts of operatorial derivations.

Spacetime is not primitive. Any "coordinates" are emergent labels of transport
parameters, not background geometry.

## 2. Hestenes Complex Structure as Axis

The complex unit is encoded as the internal axis

```
K = J ∘ ε
```

in the doubled real space. This replaces scalar `i` by a canonical operatorial
involution.

## 3. Operatorial Bohm–Madelung Split

Given a state-dependent generator `G(ψ) : EndH`, the induced dynamics is

```
δ_ψ(A) := [G(ψ), A]
```

The real doubled QGT readout splits into:

```
g_ψ(A) = metricOfOperator (δ_ψ A)
Ω_ψ(A) = berryOfOperator (δ_ψ A)
```

This is the operatorial analogue of the Madelung split into "density/metric"
and "phase/symplectic" channels, but without introducing scalar wavefunctions.

## 4. Surprisal as Modular Hamiltonian

Surprisal is encoded by the modular operator. The modular Hamiltonian is the
operatorial generator behind transport; its flow is the dissipative, non-unitary
channel, but expressed without a scalar `i`.

## 5. Source vs Gauge Branch

The operatorial split

```
relativeModularDeriv = modularGaugeDeriv + relativeModularSourceDeriv
```

is the geometric version of the "volume-preserving" versus "dilation" branches.
In Hestenes language, this is the canonical gauge/source decomposition of the
state evolution.

## 6. Phase-Axis Response

The "phase force" is measured by the response of `K`:

```
phaseAxisResponse(X) = [X, K]
```

Phase-linear generators commute with `K` and yield zero response; phase-odd
generators produce a source contribution in the doubled channel.

## 7. Welded Obstruction as Operatorial Quantum Potential

The projector obstruction operator and its Hestenes-twisted readout provide the
natural candidate for the Bohm–Madelung "quantum potential" in operatorial form.
It is not a scalar correction term, but a geometric obstruction carried by the
transported operator seed.

## 8. Current Lean Spine (Non-Scalar)

The operational skeleton is already present as operatorial definitions:

- `StateModularDatum`, `stateInducedDynamics`
- `stateQGTMetricReadout`, `stateQGTPhaseReadout`
- `phaseAxisResponse` and the phase parity split
- welded obstruction axis and its state-dependent phase readout

The goal is to keep all new statements inside this spine, avoiding diagonal
reductions or scalar effective models.

## 9. Next Formal Targets

1. State-dependent generator `G(ψ)` derived from a modular/surprisal owner.
2. A theorem that the welded obstruction readout lands in the phase-odd,
   super-even sector and controls the Berry channel.
3. A dissipation theorem: non-Hermitian evolution as the source branch in the
   doubled Hestenes geometry, with explicit metric/phase readouts.
4. A "Bohm–Madelung" theorem statement phrased entirely in terms of operator
   transport and QGT readouts.

