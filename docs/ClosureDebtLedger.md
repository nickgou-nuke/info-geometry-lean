# Closure Debt Ledger

Last updated: 2026-04-18 (Europe/Sofia)

This ledger tracks closure debt as executable proof obligations on the
operator-algebraic spine. It is not an essay surface; each row maps to Lean
anchors and CI gates.

## Debt Register

| Debt ID | Requirement | Current Formal Anchors | Missing Derivation Target | Owner Surface | Status |
|---|---|---|---|---|---|
| D1 | Prove commutator forcing (`[K, I]`) from symmetry/Cartan assumptions, not by direct commutation assumption. | `winding_orbit_periodicity` in `WindingOrbitClosure`; forcing owner `HasClockAxisForcingSeed`, `modularTransportGenerator_commutes_clockAxis_of_forcingSeed`, and `winding_orbit_periodicity_of_forcingSeed`; `modularAnomalyGenerator_eq_commutator_shadow` and `unified_anomaly_bridge` in `ModularAnomaly`; odd-sector forcing lemmas `commutator_IK_mem_odd` / `commutator_KI_mem_odd` in `CartanPhaseAxisForcing`. | Strengthen forcing predicate from phase-linearity to Cartan-grade assumptions on the target closure lane and discharge `Commute` via those assumptions. | `lean/InfoGeometry/Core/CartanPhaseAxisForcing.lean`, `lean/InfoGeometry/Canonical/WindingOrbitClosure.lean`, `lean/InfoGeometry/Quantum/ModularAnomaly.lean`. | In progress |
| D2 | Replace Drazin/Weyl placeholders with constructive spectral proofs. | `IsWeylCompatible` equivalences in `TriadicWeylBridge`; constructive owner shim `drazinInverse_isWeylCompatible` in `DrazinWeylConstructive`. | Strengthen shim assumptions from raw commutation witness to explicit constructive Drazin witness chain from spectral lane. | `lean/InfoGeometry/Canonical/DrazinWeylConstructive.lean`, `lean/InfoGeometry/Quantum/TriadicWeylBridge.lean`, `lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean`. | In progress |
| D3 | Prove Sinkhorn as defect-reduction flow (primary relative-volume monotonicity, derived odd-sector readout). | Relative-volume owner surface `δ_relVol`/`δ_volume`, `δ_relVol_nonneg`, `δ_relVol_next_le`, `SinkhornRelativeDefectBridge`, `δ_odd_next_le_of_relativeDefectBridge` in `SinkhornDefectFlow`; Sinkhorn RN barrier trajectory anchors `trajectoryRNBarrier`, `trajectoryRNBarrierNext`, `trajectoryRNBarrier_monotone` in `SinkhornFoundation`; derived router readout lane `δ_odd`, `sourcedGenerator_deviation_eq_δ_odd`, iterator theorems, and clock-defect bridge (`RouterClockDefectBridge`) in `SinkhornDefectFlow`; `sourcedGenerator_deviation_norm_le_ZD` in `TrialityMoE`; `anticommutator_QD_QD_eq_two_smul_kinetic_plus_central` in `KKTClosureSymmetry`. | Lift count→projective→relative-potential defect functional into the operator lane and derive odd-sector monotonicity from volume monotonicity (instead of postulating odd norm as primary). | `lean/InfoGeometry/LLM/SinkhornDefectFlow.lean`, `lean/InfoGeometry/Canonical/SinkhornFoundation.lean`, `lean/InfoGeometry/LLM/TrialityMoE.lean`, `lean/InfoGeometry/Canonical/KKTCore.lean`, `lean/InfoGeometry/Canonical/KKTClosureSymmetry.lean`. | In progress |
| D4 | Hard CI gates: no new `sorry`, no new `axiom`, strict build on closure trunks. | Gate script + policy + strict-check integration (this ledger cycle). | Keep gate surface green while D1-D3 theorems land. | `tools/quality/check_closure_debt_gate.py`, `tools/quality/closure_debt_gate.json`, `scripts/quality/strict-check.sh`. | Enforced |

## Gate Contract

1. `G1: No placeholder debt in closure modules`
   Command: `python3 tools/quality/check_closure_debt_gate.py --policy tools/quality/closure_debt_gate.json`
   Fails on any `sorry` or `axiom` token inside the tracked closure modules.

2. `G2: Anchor invariants`
   Same command as `G1`.
   Fails if any required theorem anchor listed in `closure_debt_gate.json` is missing.

3. `G3: Strict build of closure trunks`
   Enforced by `scripts/quality/strict-check.sh` via explicit `lake build` over closure target modules.

4. `G4: Debt ledger update discipline`
   Any PR touching D1-D3 owner modules must update this file status and targets.

## Immediate Milestones

1. D1 milestone: Cartan-grade forcing is now explicit as `IsDetailedEquilibriumSeed` (`scalePart = 0` is equilibrium-only), with a separate noncommuting lane `nonEquilibriumClockDefect` for `scalePart ≠ 0`.
2. D2 milestone: expose constructive Drazin -> Weyl preservation theorem (no nonconstructive fallback).
3. D3 milestone: P3 owner order is explicit: relative-volume RN barrier (`δ_relVol`) is primary, and odd-sector quantities (`δ_odd`, clock-defect norm channels) are derived readouts connected to detailed/non-equilibrium split.
