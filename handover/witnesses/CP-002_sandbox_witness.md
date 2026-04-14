# CP-002 Sandbox Witness (Documented, Non-Authority)

Date: 2026-04-14
Status: Exploratory witness surface

## Purpose

This document preserves the CP-002 sandbox exploration as a **witness artifact**.
It is intentionally kept outside the canonical import graph and does not define
new owner ontology.
The former sandbox module has been retired after transfer into canonical owners.

Canonical owner surfaces remain:
- `lean/InfoGeometry/Canonical/RelativeModularBlockDiagonalCore.lean`
- `lean/InfoGeometry/Canonical/RelativeModularScaleShapeSplit.lean`

## Witness Scope

The sandbox exploration attempted two speculative refinements:

1. **Potential-driven split witness**
- Idea: express scale/shape split through `RelativeModularPotential` generator form.
- Intended pattern: `generator = Shape + val • 1`, with shape projected to active lane.

2. **Operatorial Cartan witness**
- Idea: express split via spectral/geometric Cartan generators and anomaly commutator closure.
- Intended pattern: `H_gen = α • Γ_S + β • Γ_G`, then derive anomaly commutator surface.

## Why this is a witness (not canonical)

- These drafts are useful for design pressure and future theorem extraction,
  but they are not required for CP-002 closure.
- The canonical CP-002 closure is already landed via projector block diagonalization
  and Drazin/wedge compatibility on the doubled-real carrier.

## Promotion Rule

Only promote sandbox content into canonical files after:
1. file-level compile stability,
2. explicit owner placement,
3. downstream reuse signal (fan-in),
4. no ontology duplication.

Until then, treat sandbox content as witness memory, not authority.
