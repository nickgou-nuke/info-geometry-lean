# Kasparov-Krein DIII Ledger Manifest (Track B + DIII/Andreev)

Generated: 2026-06-18
Scope: freeze-first package for DIII bridge + Track B evidence

## Closed theorem surface (kernel or interface)

### Projective bridge layer

- `InfoGeometry.Projective.KasparovKreinDIIIBridge.finite_andreev_diii_signature_packet`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/Projective/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.canonical_diii_proxy_sign_readback`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/Projective/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.canonical_diii_proxy_root_readback`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/Projective/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.krein_kasparov_grade_split_from_witness`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/Projective/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.krein_kasparov_mixed_commutator_gZero`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/Projective/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.kasparov_product_cycle_readback`
  - kind: interface theorem (explicit hypothesis: `KasparovProductData` supplied)
  - owner file: `lean/InfoGeometry/Projective/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.klein_bottle_trace_absorption`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/Projective/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.concreteTopologicalSocket2_packet`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/Projective/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_sq`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/Projective/AndreevHorizonUnitarity.lean`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_normSq`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/Projective/AndreevHorizonUnitarity.lean`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_fourth`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/Projective/AndreevHorizonUnitarity.lean`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.concreteAndreevHorizon_information_preservation`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/Projective/AndreevHorizonUnitarity.lean`

### Operator-algebra bridge layer

- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.concrete_diii_andreev_bridge_packet`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_andreev_left_kasparov_defect_zero`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_andreev_right_kasparov_defect_zero`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_andreev_reflection_eq_neg_time_reversal`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_diii_time_reversal_sq`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean`
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_diii_particle_hole_sq`
  - kind: kernel theorem
  - owner file: `lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean`

## External corridor evidence (non-kernel)

- `andreev_diii_kasparov_witness.v1`
  - path: `formalizations/andreev_diii_kasparov_witness.py`
  - command: `python3 formalizations/andreev_diii_kasparov_witness.py --json`
  - acceptance: `status=verified` and `is_verified=true`
- `non_iso_conf3_rank32_external_audit.v1`
  - path: `artifacts/non_iso_conf3_rank32_external_audit.json` (or custom `--output`)
  - command: `python3 proofs/non_iso_conf3_rank32_external_audit.py --script compute_derham.m2 --m2-timeout 900`
  - acceptance: `status=verified` and `is_verified=true`
- `compute_derham_track_b.py`
  - path: `formalizations/compute_derham_track_b.py`
  - command: `python3 formalizations/compute_derham_track_b.py --launch --watch --script compute_derham.m2 --log <log>`
  - acceptance: status watch stream only; final proof decision must still come from a verified certificate payload

## Open debt list (explicit)

1. **Conservative Kasparov product theorem (real split-Krein level)**
   - owner lane: `InfoGeometry.KK.Product`, `InfoGeometry.KK.RealSplitKKTBridge`
   - assumptions: interior tensor product theorem remains an interface assumption
2. **Geometric horizon ↔ Andreev boundary identification**
   - owner lane: `InfoGeometry.Canonical` / Black-hole horizon corridor
   - assumptions: no kernel theorem currently identifies the finite corridor with the physical geometric horizon
3. **Full KO-theoretic Klein-bottle anomaly theorem**
   - owner lane: `InfoGeometry.Canonical.KleinBottleTopology`
   - assumptions: current use is finite topological glue algebra, not KO-index closure
4. **Certified Betti-to-Majorana transport**
   - owner lane: `InfoGeometry.Projective.NonIsoConf3RankIngestion`
   - assumptions: needs verified external certificate (`status=verified`) and bridge theorem into physical transport claims
5. **Finite DIII/chiral/parity ↔ anyon monodromy bridge**
   - owner lane: `InfoGeometry.Canonical.FiniteMajoranaProjectiveBraiding`
   - assumptions: conservative interface lemma still pending (finite readouts only)

## Evidence index references

- `docs/KASPAROV_KREIN_DIII_EVIDENCE_SCHEMAS.md` (schema details)
- `docs/KASPAROV_KREIN_DIII_RUNBOOK.md` (execution flow)
- `docs/KASPAROV_KREIN_DIII_LEDGER.md` (human debt ledger)
- `proofs/non_iso_conf3_rank32_external_audit.py` (Track B certificate runner)
