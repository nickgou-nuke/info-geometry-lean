# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:32.217719+00:00`
Root: `lean/InfoGeometry/Canonical/MongeAmpereDualSheetBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **57**
- Hard: **0**
- Soft: **46**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/MongeAmpereDualSheetBridge.lean` | `advisory` | 103 | 0 | 46 | 11 | 57 |

## Findings by file

### `lean/InfoGeometry/Canonical/MongeAmpereDualSheetBridge.lean`
- module: `InfoGeometry.Canonical.MongeAmpereDualSheetBridge`
- status: `advisory`
- debt_score: `103`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L29 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L63 [soft] `simp-law-injection` in `simp-declaration plusPointL_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `simp-law-injection` in `simp-declaration minusPointL_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `simp-law-injection` in `simp-declaration dualSheetLift_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `simp-law-injection` in `simp-declaration dualSheetLift_apply_plusPoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L92 [soft] `simp-law-injection` in `simp-declaration dualSheetLift_apply_minusPoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L100 [soft] `simp-law-injection` in `simp-declaration fst_dualSheetLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L107 [soft] `simp-law-injection` in `simp-declaration snd_dualSheetLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [soft] `skeletal-proof` in `theorem plusPointL_eq_adjoint_fstL` — proof appears to close via minimal tactic one-liner
  - L120 [soft] `simp-law-injection` in `simp-declaration plusPointL_adjoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L123 [advisory] `local-hypothesis-injection` in `theorem plusPointL_eq_adjoint_fstL` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L125 [soft] `simp-law-injection` in `simp-declaration fst_L_adjoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L129 [soft] `skeletal-proof` in `theorem minusPointL_eq_adjoint_sndL` — proof appears to close via minimal tactic one-liner
  - L137 [soft] `simp-law-injection` in `simp-declaration minusPointL_adjoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L140 [advisory] `local-hypothesis-injection` in `theorem minusPointL_eq_adjoint_sndL` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L142 [soft] `simp-law-injection` in `simp-declaration snd_L_adjoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L146 [soft] `simp-law-injection` in `simp-declaration dualSheetLift_star` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L154 [soft] `simp-law-injection` in `simp-declaration dualSheetLift_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L178 [soft] `simp-law-injection` in `simp-declaration plusBlockMap_dualSheetLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L185 [soft] `simp-law-injection` in `simp-declaration minusBlockMap_dualSheetLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L192 [soft] `simp-law-injection` in `simp-declaration plusToMinusBlockMap_dualSheetLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L199 [soft] `simp-law-injection` in `simp-declaration minusToPlusBlockMap_dualSheetLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L226 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_dualSheetLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L234 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_dualSheetLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L248 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L250 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L274 [soft] `simp-law-injection` in `simp-declaration plusBlockMap_dualSheetMetricOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L280 [soft] `simp-law-injection` in `simp-declaration minusBlockMap_dualSheetMetricOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L286 [soft] `simp-law-injection` in `simp-declaration plusToMinusBlockMap_dualSheetMetricOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L292 [soft] `simp-law-injection` in `simp-declaration minusToPlusBlockMap_dualSheetMetricOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L298 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_dualSheetMetricOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L304 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_dualSheetMetricOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L310 [soft] `skeletal-proof` in `theorem mongeAmpereDensityOperator_eq_smul_id_of_satisfiesMongeAmpere` — proof appears to close via minimal tactic one-liner
  - L317 [soft] `skeletal-proof` in `theorem mongeAmpereDensityOperator_eq_exp_smul_id_of_satisfiesMongeAmperePotential` — proof appears to close via minimal tactic one-liner
  - L324 [soft] `skeletal-proof` in `theorem mongeAmpereDensityOperator_eq_id_of_incompressible` — proof appears to close via minimal tactic one-liner
  - L331 [soft] `skeletal-proof` in `theorem mongeAmpereDensityOperator_eq_exp_metricLogDet_smul_id` — proof appears to close via minimal tactic one-liner
  - L338 [soft] `skeletal-proof` in `theorem spectralMongeAmpereDensityOperator_eq_exp_spectralBasepointLogVolume_smul_id` — proof appears to close via minimal tactic one-liner
  - L361 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L363 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L375 [soft] `simp-law-injection` in `simp-declaration plusBlockMap_squeezingTransport` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L394 [soft] `simp-law-injection` in `simp-declaration minusBlockMap_squeezingTransport` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L414 [soft] `simp-law-injection` in `simp-declaration plusToMinusBlockMap_squeezingTransport` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L422 [soft] `simp-law-injection` in `simp-declaration minusToPlusBlockMap_squeezingTransport` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L430 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_squeezingTransport` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L436 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_squeezingTransport` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L448 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L450 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L458 [soft] `simp-law-injection` in `simp-declaration plusBlockMap_rnEntropyDualSheetSourceOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L466 [soft] `simp-law-injection` in `simp-declaration minusBlockMap_rnEntropyDualSheetSourceOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L474 [soft] `simp-law-injection` in `simp-declaration plusToMinusBlockMap_rnEntropyDualSheetSourceOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L481 [soft] `simp-law-injection` in `simp-declaration minusToPlusBlockMap_rnEntropyDualSheetSourceOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L488 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_rnEntropyDualSheetSourceOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L503 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_rnEntropyDualSheetSourceOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L518 [soft] `skeletal-proof` in `theorem mongeAmpereDensityOperator_eq_rnEntropyDualSheetSourceOp_of_rnEntropySource` — proof appears to close via minimal tactic one-liner
  - L529 [soft] `skeletal-proof` in `theorem mongeAmpereDensityOperator_eq_exp_neg_kahlerPotentialRN_smul_id_of_rnEntropySource` — proof appears to close via minimal tactic one-liner

