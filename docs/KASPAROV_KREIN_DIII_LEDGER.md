# Kasparov-Krein DIII Ledger (Status Freeze)

**Status:** frozen snapshot for repository integration and citation reuse

- **Frozen at:** 2026-06-18
- **Scope:** finite DIII/Andreev/Klein corridor, conservative external-computation status
- **Maintainer intent:** kernel-checked claims in Lean only; external outputs are evidence-only channels.

## 1) Closed theorem surface (actively usable for Lean citations)

### Projective bridge layer

- `InfoGeometry.Projective.KasparovKreinDIIIBridge.finite_andreev_diii_signature_packet` — kernel
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.canonical_diii_proxy_sign_readback` — kernel
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.canonical_diii_proxy_root_readback` — kernel
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.krein_kasparov_grade_split_from_witness` — kernel
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.krein_kasparov_mixed_commutator_gZero` — kernel
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.kasparov_product_cycle_readback` — kernel (interface only)
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.klein_bottle_trace_absorption` — kernel
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.concreteTopologicalSocket2_packet` — kernel

### Operator-algebra bridge layer

- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.concrete_diii_andreev_bridge_packet` — kernel
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_andreev_left_kasparov_defect_zero` — kernel
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_andreev_right_kasparov_defect_zero` — kernel

### Andreev horizon readout layer (used by corridor)

- `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_sq` — kernel
- `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_normSq` — kernel
- `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_fourth` — kernel
- `InfoGeometry.Projective.AndreevHorizonUnitarity.concreteAndreevHorizon_information_preservation` — kernel

## 2) Closed external artifacts (evidence-only, non-authoritative)

- `formalizations/andreev_diii_kasparov_witness.py --json` → `andreev_diii_kasparov_witness.v1`
- `formalizations/andreev_horizon_witness.py` (human-readable finite witness)
- `proofs/non_iso_conf3_rank32_external_audit.py` → `non_iso_conf3_rank32_external_audit.v1`
- `formalizations/compute_derham_track_b.py` (watch/launch helper)

See `docs/KASPAROV_KREIN_DIII_EVIDENCE_SCHEMAS.md` for schema examples.

## 3) Open closure debt (explicit assumptions/owners)

1. **Conservative Kasparov product theorem (interior tensor) at the real split-Krein level**
   - **Owner lane:** `InfoGeometry.KK.Product`, `InfoGeometry.KK.RealSplitKKTBridge` / `InfoGeometry.OperatorAlgebra.ConstructiveKasparovBoundary`
   - **Assumptions left:** interior product construction and compatibility lemmas are currently postulated as interface data in `kasparov_product_cycle_readback`.

2. **Geometric realization of causal horizons as Andreev boundaries**
   - **Owner lane:** `InfoGeometry.Canonical.BlackHoleInformationParadox`, `InfoGeometry.Canonical.RealBdGDIIIAtom`
   - **Assumptions left:** no kernel theorem identifies the physical boundary model with the finite Andreev/DIII packet from this corridor.

3. **Full KO-theoretic Klein-bottle anomaly theorem**
   - **Owner lane:** `InfoGeometry.Canonical.KleinBottleTopology`, `InfoGeometry.Canonical.KleinBottleBoundaryAction`
   - **Assumptions left:** current use of `klein_topology_trace_closure` is matrix/finitary and does not yet discharge KO-index claims for geometric quotients.

4. **Certifying external Track-B Rank-32 certificate into a Majorana-mode theorem**
   - **Owner lane:** `InfoGeometry.Projective.NonIsoConf3RankIngestion`, `InfoGeometry.Projective.BlackHoleUnitarityBridge`
   - **Assumptions left:** requires externally verified `(is_verified=true, status="verified")` payload + theorem bridge from Betti certificate to physical mode-transfer claim.

5. **Fibonacci anyon / monodromy consequences under finite DIII/parity readouts**
   - **Owner lane:** `InfoGeometry.Canonical.FiniteMajoranaBraiding`, `InfoGeometry.Canonical.FiniteMajoranaProjectiveBraiding`, `InfoGeometry.Projective.Topology`
   - **Assumptions left:** pending bridge lemma to map finite Möbius-DIII readout hypotheses to existing braid/monodromy invariants without physical overclaim.

## 4) Safe citation policy

- For theorem statements and proofs, cite only the **closed theorem surface**.
- For pipeline or pipeline-like documentation, always include explicit `is_verified` / `status` checks for artifact lanes.
- Never collapse artifact non-verified statuses into theorem-level truth.
