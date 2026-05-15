# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:49.759714+00:00`
Root: `lean/InfoGeometry/Canonical/RelationalInformationCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **11**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelationalInformationCore.lean` | `advisory` | 28 | 0 | 11 | 6 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelationalInformationCore.lean`
- module: `InfoGeometry.Canonical.RelationalInformationCore`
- status: `advisory`
- debt_score: `28`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L39 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L70 [soft] `law-field-locker` in `structure-field RelationalInformationDatum.informationFunctional` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field RelationalInformationDatum.firstVariation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field RelationalInformationDatum.secondVariation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L114 [soft] `simp-law-injection` in `simp-declaration channelPhaseAxis_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L119 [soft] `simp-law-injection` in `simp-declaration channelPhaseAxis_apply_eq_comp_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L135 [advisory] `local-hypothesis-injection` in `theorem channelPhaseAxis_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L142 [advisory] `local-hypothesis-injection` in `theorem channelPhaseAxis_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L154 [soft] `simp-law-injection` in `simp-declaration comparisonGeneratorPhase_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L211 [soft] `simp-law-injection` in `simp-declaration comparisonMetricReadout_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L220 [soft] `simp-law-injection` in `simp-declaration comparisonPhaseReadout_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L240 [soft] `simp-law-injection` in `simp-declaration comparisonPhaseReadout_eq_metric_comp_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L251 [soft] `simp-law-injection` in `simp-declaration comparisonPhaseReadout_eq_metric_comp_modularComplexI` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L284 [soft] `simp-law-injection` in `simp-declaration transportObstruction_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L289 [advisory] `local-hypothesis-injection` in `def transportObstruction` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

