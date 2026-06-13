# Klein Berry / Boundary / Bott API

> Status: finite bridge index
> Audited: 2026-06-11
> Boundary: this page records the repo-owned finite bridge from Berry holonomy
> to the Klein boundary action and the Bott-periodic split Clifford carrier.

This page is the practical map for the finite Berry/Klein/Bott corridor.

## Primary Lean Owner

- `lean/InfoGeometry/Canonical/KleinBerryBoundaryBottBridge.lean`

## What The Bridge Actually Packages

- `KleinBerryPhase`
  - orientable holonomy witness `B_EP * B_EP = -1`
  - Klein-twisted holonomy cancellation `B_EP * (G_Glide * B_EP * G_Glide) = 1`

- `KleinBottleBoundaryAction`
  - finite `Z₂` glide-reflection packet
  - involutive sheet/deck actions

- `CliffordBott`
  - direct-limit split Clifford carrier `Cl_infty`
  - square-zero lift of the finite nilpotent shield

## Proof Boundary

This bridge is a theorem-safe packaging layer.
It does not prove:

- a general KR-theory cascade,
- a K-theoretic T-duality theorem,
- a global cobordism classification,
- or a full physical holonomy/parallel-transport theory.
