# Kasparov-Krein DIII + Track B Freeze Runbook (v1)

## Scope and intent

This runbook is the freeze-first operational contract for the DIII/Andreev corridor.

- **Status target:** no new speculative claims; only kernel-checked theorems + explicit evidence lanes.
- **Primary surfaces:** `Projective` bridge module, `OperatorAlgebra` bridge module, external Track B artifacts.
- **Rule of use:** if a target is not `verified` it is not theorem evidence.

## 1) Runbook flow (what to execute)

### A. Lean kernel checks (authoritative)

```bash
cd /home/goutev/repos/info-geometry-lean

# Core bridge modules
lake env lean lean/InfoGeometry/Projective/KasparovKreinDIIIBridge.lean
lake env lean lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean

# Umbrella checks
lake env lean lean/InfoGeometry/Projective/All.lean
lake env lean lean/InfoGeometry/OperatorAlgebra/All.lean
```

### B. SymPy finite verification (evidence only)

```bash
cd /home/goutev/repos/info-geometry-lean
python3 formalizations/andreev_horizon_witness.py
python3 formalizations/andreev_diii_kasparov_witness.py
python3 -m py_compile formalizations/andreev_diii_kasparov_witness.py formalizations/andreev_horizon_witness.py
python3 formalizations/andreev_diii_kasparov_witness.py --json --out /tmp/andreev_diii_witness.json
```

### C. Track B (external Betti/derham evidence)

#### Fast/lighter lane (finite field / singular diagnostics)

```bash
cd /home/goutev/repos/info-geometry-lean
python3 scripts/experiments/DeRhamKleinQuadric/audit_rank32.py \
  --dim 4 \
  --signature euclidean \
  --run finite_field singular sage \
  --fields 2,3,5 \
  --out /tmp/rank32_diagnostic.json
```

#### Full Track B lane (Macaulay2)

```bash
cd /home/goutev/repos/info-geometry-lean
python3 scripts/experiments/DeRhamKleinQuadric/audit_rank32.py \
  --dim 4 \
  --signature euclidean \
  --run macaulay2 \
  --m2-timeout 900 \
  --m2-derham \
  --m2-method dlocalize-ext \
  --out /tmp/rank32_m2_dlocalize_900s.json
```

#### External-track hardening helper

```bash
cd /home/goutev/repos/info-geometry-lean
python3 proofs/non_iso_conf3_rank32_external_audit.py \
  --script compute_derham.m2 \
  --m2-timeout 900 \
  --output artifacts/non_iso_conf3_rank32_external_audit.json \
  --log artifacts/non_iso_conf3_rank32_external_audit.log

python3 formalizations/compute_derham_track_b.py \
  --launch \
  --script compute_derham.m2 \
  --log /tmp/compute_derham_track_b.out \
  --json
```

## 2) Verification status ontology

Use **explicit status gates** at every publication boundary:

| Source | Accepted status | is_verified | Meaning |
|---|---|---|---|
| Lean compilation/tests | exit=0 + no diagnostics | n/a | Kernel checked and importable |
| `andreev_diii_kasparov_witness.v1` | `status=verified` | true | finite DIII/Andreev algebraic witness pass |
| `non_iso_conf3_rank32_external_audit.v1` | `status=verified` | true | externally verified Betti certificate payload |
| `compute_derham_track_b.py` | `status=completed` | n/a (watch payload only) | process lifecycle finished, parse markers still required for theorem use |

Hard fail markers for promotion:

- `status=fallback`, `status=timeout`, `status=execution-failed`, `status=parse-failed`, `status=missing-backend`, `is_verified=false`

### Required command provenance fields

For each heavy/unstable external invocation, record at minimum:

- command string
- process id (if background)
- exit status / timeout reason
- artifact path
- marker evidence (e.g. `AFTER_DE_RHAM`, `BETTI=`, `TOTAL=` when available)

Store this in your run notebook or the artifact manifest below.

## 3) Canonical theorem citation surface for this layer

Use these names directly in docs and theorem references:

**Projective layer**
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.finite_andreev_diii_signature_packet`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.canonical_diii_proxy_sign_readback`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.canonical_diii_proxy_root_readback`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.krein_kasparov_grade_split_from_witness`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.krein_kasparov_mixed_commutator_gZero`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.kasparov_product_cycle_readback`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.klein_bottle_trace_absorption`
- `InfoGeometry.Projective.KasparovKreinDIIIBridge.concreteTopologicalSocket2_packet`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_sq`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_normSq`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.andreevTwin_fourth`
- `InfoGeometry.Projective.AndreevHorizonUnitarity.concreteAndreevHorizon_information_preservation`

**Operator-algebra layer**
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.concrete_diii_andreev_bridge_packet`
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_andreev_left_kasparov_defect_zero`
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_andreev_right_kasparov_defect_zero`
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_andreev_reflection_eq_neg_time_reversal`
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_diii_time_reversal_sq`
- `InfoGeometry.OperatorAlgebra.KasparovKreinDIIIBridge.finite_diii_particle_hole_sq`

## 4) Evidence artifacts index (expected locations)

- `docs/KASPAROV_KREIN_DIII_MANIFEST.md` (human manifest + closed/debt ledger)
- `artifacts/non_iso_conf3_rank32_external_audit.json`
- `artifacts/non_iso_conf3_rank32_external_audit.log`
- `proofs/non_iso_conf3_rank32_external_audit.py`
- `formalizations/compute_derham_track_b.py`
- `formalizations/andreev_diii_kasparov_witness.py`
- `formalizations/andreev_horizon_witness.py`

Schema examples are in `docs/KASPAROV_KREIN_DIII_EVIDENCE_SCHEMAS.md`.

## 5) Freeze checklist

- [ ] `lake env lean lean/InfoGeometry/Projective/KasparovKreinDIIIBridge.lean`
- [ ] `lake env lean lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean`
- [ ] `lake env lean lean/InfoGeometry/Projective/All.lean`
- [ ] `lake env lean lean/InfoGeometry/OperatorAlgebra/All.lean`
- [ ] SymPy witnesses run in plain mode and `--json` for `andreev_diii_kasparov_witness.py`
- [ ] Track B `non_iso_conf3_rank32_external_audit.py` either yields verified payload or explicit timed-failed log entry
- [ ] `docs/KASPAROV_KREIN_DIII_SYNTHESIS.md`, `docs/KASPAROV_KREIN_DIII_LEDGER.md`, and this runbook are aligned
- [ ] Debt items stay enumerated and are not promoted into physical theorems

## 6) Safe separation rules

1. Lean kernel theorems are the top-tier citation base.
2. SymPy scripts are finite algebra checks (supporting evidence only).
3. Macaulay2 Track B outputs are external numerical certificates and require `schema/status` gate.
4. Open debt stays explicit and hypothesis-level until a theorem-level bridge is produced.
