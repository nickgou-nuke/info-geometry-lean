# Bregman / Jacobian / Yang--Lee provenance closure decision table

Generated after `sandbox/run_deep_audit_recovery_bregman_yanglee.py` completed on 2026-07-13.

## Scanner inventory validation

Artifacts:

- `sandbox/deep_audit_recovery_bregman_yanglee.json` (about 9.1 GiB)
- `sandbox/deep_audit_recovery_bregman_yanglee.md` (about 3.1 GiB)
- Working ledger: `sandbox/bregman_jacobian_yanglee_owner_ledger.md`

Extracted top-level counts from the generated JSON:

| field | value |
|---|---:|
| files seen | 527094 |
| files read | 147996 |
| bytes read | 45087107904 |
| matching files | 97575 |
| matching lines | 5222372 |
| skipped large files | 146 |
| archive members read | 7908 |
| source/diff classified hits | 18541 |
| prose/transcript classified hits | 79034 |
| truncation records | 20561 |
| read errors | 0 |

Caps / truncation:

- File cap: 64 MiB.
- Excerpt cap: 80 contextual excerpts per matching file.
- SQLite transcript cap: 200000 rows per table.
- No read errors were reported.
- Many truncation records are excerpt caps, including Mathlib/zeta files.

Scanner caveat:

- The scanner surface list included `.lake`; this is noisy and violates the desired dependency-lockdown discipline for future manual inspection. No edits were made there, but future provenance scans should structurally exclude `.lake/packages` rather than merely skip common names during recursive walks.

## Exact relevant source/diff hits

A filtered pass over `artifacts[]` for exact declaration/path symbols produced 29 source/diff hits. Relevant buckets:

1. Hermes paste snippets:
   - `/home/goutev/.hermes/pastes/paste_32_051838.txt`
   - `/home/goutev/.hermes/pastes/paste_33_052439.txt`
   - `/home/goutev/.hermes/pastes/paste_34_055328.txt`
   - `/home/goutev/.hermes/pastes/paste_35_063745.txt`

   These are transcript/proposal prose with Lean snippets, not canonical source files. They explain the requested SL2/Jacobian/log-norm/two-phase theorem targets and later dedup instructions.

2. Native Lee--Yang/Asano archived source hits:
   - `info-geometry-lean-epoch3-codex-export/lean/InfoGeometry/Analysis/AsanoContractionNative.lean`
   - `.../Canonical/LeeYangAsanoDigest.lean`
   - `.../Canonical/LeeYangAsanoNativeCore.lean`
   - `.../Canonical/LeeYangAsanoMobiusNative.lean`
   - `.../Canonical/LeeYangAsanoFullReduction.lean`
   - `.../Canonical/LeeYangAsanoEndpointNative.lean`
   - `.../Canonical/LeeYangAsanoKleinV4Compactification.lean`
   - `.../Canonical/LeeYangStabilityPacket.lean`
   - prime Lee--Yang bridge/limit files.

   These map to existing live canonical owners. They are not two-phase free-energy algebra and do not duplicate `ComplexThermodynamicLift.twoPhasePartition`.

3. Bregman archived source hits:
   - archived `Thermo/FromBregman.lean` copies in epoch/fusion/main archive surfaces.

   These map to the existing live owner `lean/InfoGeometry/Thermo/FromBregman.lean`.

4. Complex thermodynamic archived source hit:
   - archived `Thermo/ComplexThermodynamicLift.lean` has the earlier first-law/Bregman/Cayley material but not the current two-phase section.

## Owner / provenance decisions

| Item | Existing canonical owner | Recovery/provenance result | Decision |
|---|---|---|---|
| Finite two-phase algebra: `freeEnergyGap`, `twoPhasePartition`, `twoPhasePartition_factor`, `twoPhasePartition_eq_zero_iff`, `yangLeeZero_freeEnergyGap`, `yangLeeZero_realPhaseConditions` | `lean/InfoGeometry/Thermo/ComplexThermodynamicLift.lean` | Hermes paste requested target; archived `ComplexThermodynamicLift` predates this section. Duplicate temporary topology copy was removed. | Keep only in `ComplexThermodynamicLift`. No topology duplicate. |
| Transparent free-energy-gap readback | `ComplexThermodynamicLift.lean` | Direct definitional readback; no separate archive owner found. | Keep as a harmless owner-local readback. |
| Finite Bregman/Gibbs/free-energy construction | `lean/InfoGeometry/Thermo/FromBregman.lean` | Archived copies match the existing owner lineage. | Existing canonical owner; do not recreate. |
| Finite log-det/Burg-to-Gibbs free-energy construction | `lean/InfoGeometry/Thermo/FromLogDet.lean` | Semantic audit shows this is the theorem-honest determinant/log-volume-to-finite-Gibbs lane. | Use this owner for future determinant/SPD bridges; do not identify raw Möbius Jacobian by name alone. |
| Finite Möbius/Souriau permutation invariance | `lean/InfoGeometry/Topology/MobiusSouriauThermodynamicFlow.lean` | No committed Git ancestor; provenance from Pi/Codex session, not archive. | Staged addition; theorem strength is finite permutation invariance under explicit realization hypotheses. |
| SL2 finite flow / Riccati / denominator / Jacobian / log-norm corridor | `lean/InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean` | No committed Git ancestor and no exact archived source file. Pi/Codex session records incremental compiled construction. Hermes pastes are proposal/prose, not source. | Classify as newly synthesized/reconstructed from live session work, not exact archived recovery. Keep quarantined as staged addition until owner integration decision. |
| `boltzmannLogJacobianEntropy` | `ThermodynamicSL2MobiusFlow.lean` | No prior canonical owner found. It is definitionally `kB * logJacobianNorm`, with explicit warning that it is not normalized Gibbs/von Neumann entropy. | Keep only if SL2 owner is accepted; otherwise quarantine with SL2 file. |
| Native Lee--Yang/Asano hierarchy | `Analysis/AsanoContractionNative.lean`, `Canonical/LeeYangAsano*.lean`, `Canonical/PrimeLeeYang*.lean` | Archived epoch source maps to existing live owners. | Existing canonical hierarchy; do not merge two-phase algebra into these unless a typed bridge is proved. |
| Bregman--Jacobian--Yang--Lee bridge | none | No recovered theorem found that identifies Möbius Jacobian log norm with Legendre/Bregman energy or finite Gibbs free energy. | Genuine missing bridge, but blocked pending explicit carrier/hypotheses. |

## Import / downstream use summary

- `ComplexThermodynamicLift` is imported by `lean/InfoGeometry/All.lean`, `src/infogeometry/lean/InfoGeometry/All.lean`, and its sandbox test.
- `FromBregman` has many downstream consumers: `Thermo/All`, `Thermo/AmariSouriauBridge`, `OptimalTransport`, `Arithmetic/PrimonChiralSouriauThermodynamics`, canonical bridge files, and umbrella imports.
- `MobiusSouriauThermodynamicFlow` is imported by `Topology/All.lean` and its sandbox.
- `ThermodynamicSL2MobiusFlow` is imported by `Topology/All.lean` and its sandbox only.
- Lee--Yang/Asano owners form an existing canonical/analysis hierarchy with umbrella imports and archived source correspondences.

## Integration gate

Do not add more Lean bridge theorems until an explicit model supplies:

1. a typed map from Möbius/SL2 Jacobian data to an existing Bregman/Legendre/log-det carrier;
2. hypotheses proving that map gives the intended energy or potential, not only a similar formula;
3. a finite state space or an explicitly justified continuous owner;
4. a typed complexification into `ComplexThermodynamicLift.twoPhasePartition` if Yang--Lee cancellation is desired.

Current selected action: provenance closure only; no new mathematical integration.
