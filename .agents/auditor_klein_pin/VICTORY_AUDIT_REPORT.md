# Corrective scope report: Klein Pin structures

## Status

The earlier report in this file was withdrawn because it asserted geometric Pin
claims that the Lean source does not establish. This document records a
corrective source-level review, not an independent QMS audit.

## Verified source scope

`lean/InfoGeometry/Topology/KleinPinStructures.lean` now proves the following
algebraic statement: if `z` is central and `z * z = 1`, then for `b = 1` or
`b = z`, conjugation by any group element fixes `b`, hence equals `b⁻¹`.

The targeted locked Lake build for
`InfoGeometry.Topology.KleinPinStructures` passed after this correction.

## Claims not established

The module defines no `Pin(2)` group, map to `O(2)`, frame bundle, Klein bottle
holonomy representation, geometric lift, or theorem classifying four Pin
structures. Therefore the previous claims of a modeled central extension,
existence of four lifts, and completed geometric classification were false and
must not be cited as verified results. Independent QMS approval has not been
performed for the corrected scope.
