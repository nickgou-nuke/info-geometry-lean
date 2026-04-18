# Rigorous Derivation Queue

Last updated: 2026-04-18 (Europe/Sofia)

This file tracks unresolved derivation obligations where closure currently
depends on assumptions rather than root-forced algebra.

Companion execution surface:
- [ClosureDebtLedger.md](ClosureDebtLedger.md)

## Target A: Clock-Axis Commutation In Winding Closure

Current dependency:
- [lean/InfoGeometry/Canonical/WindingOrbitClosure.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/WindingOrbitClosure.lean): `winding_orbit_periodicity` requires `hComm : Commute K (clockAxis H)`.

Gap:
- periodicity is proven only under an external commutation hypothesis.

Required derivation path:
1. Introduce an operator-side symmetry predicate for the modular generator lane
   (potential or grading symmetry).
2. Prove a bridge theorem deriving `Commute K (clockAxis H)` from that predicate.
3. Add a theorem variant `winding_orbit_periodicity_of_symmetry` that consumes
   the derived commutation theorem instead of raw `hComm`.

Status: `open`.

## Target B: Drazin/Weyl Compatibility For Inverse Lane

Context:
- Weyl compatibility is formalized in
  [lean/InfoGeometry/Quantum/TriadicWeylBridge.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Quantum/TriadicWeylBridge.lean).
- Constructive Riesz/Drazin interfaces are in
  [lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean).

Gap:
- missing explicit theorem that the chosen Drazin inverse preserves Weyl
  sheet-compatibility under commuting constraints.

Required derivation path:
1. State a theorem target connecting Drazin witness commutation to Weyl
   compatibility of the inverse candidate.
2. Route through the Riesz/Drazin witness package (`RieszDrazinData` or
   constructive candidate lane) rather than ad hoc choice.
3. Export the theorem into the Triadic/Weyl translator lane.

Status: `open`.

## Target C: Router Residual Equals Observer Defect By Construction

Current dependency:
- [lean/InfoGeometry/LLM/TrialityMoE.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/LLM/TrialityMoE.lean): `RouterDefectBridge.residual_eq_observerDefect` is a structure field assumption.

Gap:
- bridge identity is injected as an assumption, not derived from a closure/limit
  theorem.

Required derivation path:
1. Formalize a router iteration object and residual sequence.
2. Connect sequence convergence to observer-defect residual on the canonical lane.
3. Replace direct assumption usage with a theorem-backed constructor or a
   stronger structure carrying proof obligations.

Status: `open`.

## Closure Policy

- No new capstone claims should consume these assumptions without explicit
  reference to this queue.
- Preferred output is theorem-level replacement, not new prose wrappers.
