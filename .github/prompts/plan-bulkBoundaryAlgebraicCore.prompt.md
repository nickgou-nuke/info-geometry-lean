## Plan: Algebraic Bulk-Boundary Core

Deliver the finite-dimensional algebraic core first: prove that a polarization-odd endomorphism forces a nontrivial kernel when plus/minus sector dimensions mismatch, and extract an explicit zero-mode witness. This stays axiom-free and defers chain-level bulk-boundary bridging to a follow-up theorem layer with explicit hypotheses.

**Steps**
1. Phase 1: Create a new module BulkBoundary.lean under lean/InfoGeometry/Quantum.
2. Define the local operator layer (EndS, HasZeroMode, PolarizationOdd) in ContinuousLinearMap form, aligned with RealMajorana.
3. Implement sector-swap lemmas maps_plus_to_minus and maps_minus_to_plus using existing polarization membership facts.
4. Define restricted linear maps toMinus and toPlus between polarization submodules. This can run in parallel with final cleanup of step 3.
5. Prove helper theorem: nontrivial kernel implies explicit nonzero witness via Submodule.ne_bot_iff.
6. Prove hasZeroMode_of_dim_mismatch by contradiction:
7. Assume ker H = bot, derive injectivity of H.
8. Lift injectivity to restricted maps plus -> minus and minus -> plus.
9. Apply finite-dimensional injective-map rank monotonicity twice to get finrank plus <= finrank minus and finrank minus <= finrank plus.
10. Conclude finrank equality, contradict mismatch hypothesis, discharge HasZeroMode.
11. Prove exists_zeroMode_of_dim_mismatch by composing the witness lemma with hasZeroMode_of_dim_mismatch.
12. Phase 3: Keep this module isolated from unrelated dirty files; optionally wire into canonical umbrella only after targeted build passes.

**Relevant files**
- lean/InfoGeometry/Quantum/RealMajorana.lean — KPolarization and plus/minus infrastructure to reuse.
- lean/InfoGeometry/Quantum/RealMajorana.lean — membership lemmas needed for odd-map sector transfer proofs.
- lean/InfoGeometry/Quantum/KitaevChain.lean — deferred next-phase bridge target via topologicalIndexZ2.
- lean/InfoGeometry/Canonical/Quantum.lean — optional import wiring point.
- lean/InfoGeometry/Canonical/All.lean — optional publication-surface export point.

**Verification**
1. Build focused target: lake build InfoGeometry.Quantum.BulkBoundary.
2. If umbrella imports are touched: lake build InfoGeometry.Canonical.Quantum.
3. Run workspace error scan on touched files and ensure no new diagnostics.
4. Optional final confidence pass: lake build InfoGeometry.

**Decisions**
- Scope locked to algebraic core first.
- No new axioms; future bridge theorems use explicit assumptions in signatures.
- Excluded now: concrete globalChainOperator construction and full boundary-localization theorem.

**Further Considerations**
1. Choose whether to expose the new module through canonical umbrella imports in this same changeset or keep direct-import only until the bridge phase lands.
2. In the next phase, choose bridge strength: parity-level existence theorem first, or boundary-localized zero-mode theorem with an explicit localization predicate.
