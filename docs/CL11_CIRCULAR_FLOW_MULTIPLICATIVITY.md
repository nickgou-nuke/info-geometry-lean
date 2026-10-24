# Multiplicative times of the existing circular Cl11 flow

The carrier and multiplication are `Cl11CoordinateAlgebra.Cl11` and its
installed Clifford product. The map is the existing `modularFlowCl11 t` in
`Physics.BostConnesThermalTime`; its additive equivalence and inverse at `-t`
are already proved. The same owner proves a multiplication counterexample
at `pi/4`.

Contract: multiplication is preserved for every pair iff `sin(2*t)=0`,
equivalently `t=k*pi/2` for an integer `k`. Under that exact condition, bundle
the existing additive equivalence as a native Mathlib `RingEquiv`.
Identify these admissible maps explicitly as either the identity or
`q ↦ e1Basis*q*e1Basis`; the latter occurs at `pi/2`.
Necessity uses the actual `e1Basis*e2Basis` product, and sufficiency uses
`cos(2*t)=1` or `-1` in the native coordinate product.

Maintained-source reference search found the map's laws in its owner,
aggregate imports, and the import in `BostConnesDirichletTopological`.
`Canonical.Cl11LorentzAction` has a hyperbolic operator construction on a
different carrier; it is not substituted for the map under examination.
No C*-algebra modular-flow interpretation is asserted. This classifies the
existing circular maps, not all automorphisms of the Clifford algebra.

Verification passed: parent locked session 32032 and independent QA session
50780 both completed successfully (3096 jobs). Seven axiom reports contain
exactly `[propext, Classical.choice, Quot.sound]`; four examples compiled.
There are zero source warnings and two package notices. Independent semantic
review passed, strict screening reports zero traps, and scoped diffs are clean.
Logs: `/tmp/cl11-circular-audit.log` and `/tmp/cl11-circular-qa.log`.
