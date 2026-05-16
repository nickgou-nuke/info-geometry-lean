# Native Closure Debt Execution Plan

Date: 2026-05-16
Repo: /home/goutev/repos/info-geometry-lean

## Goal
Replace witness-gated and externally-certificate-backed Lean surfaces with native kernel-checked proof chains, while keeping any unresolved claim as explicit closure debt.

## Working rule
Do not treat a bridge, alias, or stored witness packet as closure. A target is only discharged when the repository contains a native theorem term that proves the claim without external certificates, deferred assumptions, or witness-only packaging.

## Phase 1 selection logic
1. Start with the smallest modules that already expose a closure-debt socket.
2. Prefer files with explicit finite theorem content and minimal dependency fan-out.
3. Leave large interface-heavy bridge files for later unless they already contain a direct theorem candidate.

## Phase 1 targets
1. `lean/InfoGeometry/Canonical/GeometricFreudenthalBoundary.lean`
   - Status: witness interface only; no direct theorem replacement yet.
   - Action: identify the first theorem-bearing file behind the bridge and move closure there.
2. `lean/InfoGeometry/Arithmetic/PrimeMajoranaWittenCharacter.lean`
   - Status: mostly native finite theorem aliases; one infinite bridge socket remains.
   - Action: keep the finite character theorems native and track the infinite zeta bridge as explicit debt.
3. `lean/InfoGeometry/Canonical/PrimeGasWeylCharacterBridge.lean`
   - Status: bridge packet with stored equality fields.
   - Action: search for a theorem-backed owner file that can replace the stored comparisons.
4. `lean/InfoGeometry/OperatorAlgebra/AndreevHorizonBridge.lean`
   - Status: bridge-style surface in the phase-1 set.
   - Action: replace any witness field that can be discharged by a native theorem.
5. `lean/InfoGeometry/OperatorAlgebra/BaryonAsymmetryWitness.lean`
   - Status: witness-gated by name and likely debt-bearing.
   - Action: separate native invariant from any placeholder witness record.
6. `lean/InfoGeometry/Arithmetic/ProjectivePrimePartition.lean`
   - Status: theorem-bearing arithmetic target with likely finite closure path.
   - Action: prove the smallest local statement natively and keep only the irreducible remainder as debt.
7. `lean/InfoGeometry/Canonical/PrimeGasSuperKMSBridge.lean`
   - Status: bridge surface connecting thermodynamic and algebraic readouts.
   - Action: move toward a theorem-backed owner/translator chain.
8. `lean/InfoGeometry/Arithmetic/PrimeMajoranaOPE.lean`
   - Status: compact arithmetic target with explicit bridge language.
   - Action: convert the easiest witness-gated theorem first, then re-audit the rest.

## Per-module loop
1. Read the module and locate the exact witness-gated declaration.
2. Identify the nearest theorem-owned source that already proves the intended invariant.
3. Replace the witness-only packaging with a theorem-backed definition or theorem.
4. Rebuild only the touched module or the narrow owner chain.
5. Record any remaining gap as explicit closure debt with exact premises and target.

## Exit criteria for the batch
- the chosen module compiles with a native proof term for the target claim, or
- the remaining gap is documented as explicit closure debt with no false closure language.
