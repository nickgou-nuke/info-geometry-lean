# Goal: Fréchet–Leibniz n-operator Onsager bridge

Status: active implementation goal; this file is a theorem contract, not a
kernel-checked theorem.

## Current verified finite slice

`InfoGeometry.Canonical.FrechetLeibnizOnsagerBridge` proves a finite
directional log-partition/BKM readout as an `OnsagerCasimirSystem` with an
explicitly zero reversible component. It also proves the BKM response of
operator-valued one-forms and the diagonal vanishing of an explicitly
scalarized alternating two-form probe. This does not yet prove a genuine
arbitrary-degree CE differential, a nonzero curvature response, or a general
Fréchet-to-derivation theorem.

## Remaining goal

Implement, with genuine kernel-checked lemmas and the smallest existing
carriers:

1. An arbitrary-degree derivation-form differential with `d² = 0`, plus
   explicit low-degree transport to the existing CE owners.
2. A genuine continuous Fréchet jet carrier, kept distinct from alternating
   derivation forms, with proved compatibility maps where a concrete model
   supplies them.
3. A curvature-derived reversible scalar response using an explicit BKM probe,
   not an assumption field or an untyped scalarization.
4. A finite total response theorem combining the proved BKM symmetric part and
   the scalarized curvature skew part.
5. A metriplectic readout only after its force carrier and endomorphism have
   been explicitly constructed.
6. Colimit transport only conditionally on an actually specified compatible
   colimit functional.

## Non-goals

Do not promote structure fields, zero witnesses, lexical evidence, prose
claims, scalar stubs, or assumed compatibility packets as mathematical
results. Do not claim universal infinite-dimensional, physical-flow, or
colimit existence theorems without their own proved owners.
