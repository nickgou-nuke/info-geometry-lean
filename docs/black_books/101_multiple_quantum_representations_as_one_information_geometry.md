# Multiple Quantum Representations as One Information Geometry

## Main finding

The strongest repo-safe statement is:

different quantum formulations can be organized as **different presentations of one invariant package**, but only if the invariants are stated explicitly.

This avoids two failure modes:

1. collapsing all representations into a slogan with no typed contract,
2. treating every presentation as disconnected ontology.

In repo terms, this is a translator problem with closure owned by Lean.

## What is already stable

The current architecture already supports the invariant/presentation split:

- support-restricted operator lanes (`Delta`-first, projector-controlled),
- spectral/metric split handling via Drazin and Moore-Penrose packages,
- doubled/Krein transport grammar,
- scalar readouts treated as derived shadows rather than roots.

This is exactly the right substrate for a multi-presentation dictionary.

## Safe claim boundary

What is safe today:

- standard textbook picture changes (state-vs-observable time dependence),
- phase-space, hydrodynamic, stochastic, and operator-algebraic lanes can be compared through preserved structures,
- the repository already contains partial bridges across these lanes.

What is not yet safe as a theorem:

- one completed global equivalence theorem stating all lanes are already fully welded.

So the correct status is:

formal kernel + partial intertwiners + open capstone closure.

## Programmatic consequence

The next Lean move is to encode presentation-level invariants directly:

- state support,
- observable action,
- generator compatibility,
- readout compatibility (metric/phase style shadows),
- typed intertwiners between presentations.

This turns the idea from narrative to executable mathematics.

## New implementation lane

A new canonical scaffold file now exists:

`lean/InfoGeometry/Canonical/QuantumPresentation.lean`

It introduces:

- `PresentationLane` (`wavefunction`, `operator`, `phaseSpace`, `hydrodynamic`, `stochastic`, `doubledKrein`),
- `QuantumPresentation` (minimal invariant package),
- `Intertwiner` (typed representation morphism),
- `ReadoutPreservation`,
- identity and composition of intertwiners.

This file is intentionally translator-level. It does not claim grand closure.

## Repository doctrine from this chapter

The right slogan is:

“One invariant geometry, many lawful presentations.”

But the enforcement surface is not prose. It is:

- typed invariant structures,
- typed intertwiners,
- closure gates,
- kernel-checked proofs.

