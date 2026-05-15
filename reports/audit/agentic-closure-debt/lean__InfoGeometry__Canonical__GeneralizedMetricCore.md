# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:09.813213+00:00`
Root: `lean/InfoGeometry/Canonical/GeneralizedMetricCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **35**
- Hard: **0**
- Soft: **19**
- Advisory: **16**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GeneralizedMetricCore.lean` | `advisory` | 54 | 0 | 19 | 16 | 35 |

## Findings by file

### `lean/InfoGeometry/Canonical/GeneralizedMetricCore.lean`
- module: `InfoGeometry.Canonical.GeneralizedMetricCore`
- status: `advisory`
- debt_score: `54`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L42 [soft] `law-field-locker` in `structure-field GeneralizedMetricSeed.eta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field GeneralizedMetricSeed.polarization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field GeneralizedMetricSeed.metricOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field GeneralizedMetricSeed.eta_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field GeneralizedMetricSeed.polarization_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field GeneralizedMetricSeed.eta_polarization_anticommute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field GeneralizedMetricSeed.metric_eq_eta_comp_polarization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L128 [advisory] `local-hypothesis-injection` in `theorem GeneralizedMetricSeed.polarization_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L145 [advisory] `local-hypothesis-injection` in `theorem GeneralizedMetricSeed.polarization_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L162 [advisory] `local-hypothesis-injection` in `theorem GeneralizedMetricSeed.polarization_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L183 [advisory] `local-hypothesis-injection` in `theorem GeneralizedMetricSeed.polarization_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L196 [soft] `simp-law-injection` in `simp-declaration GeneralizedMetricSeed.eta_comp_metric_eq_polarization` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L202 [soft] `simp-law-injection` in `simp-declaration GeneralizedMetricSeed.metric_comp_polarization_eq_eta` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L213 [soft] `simp-law-injection` in `simp-declaration GeneralizedMetricSeed.polarization_comp_eta_eq_neg_eta_comp_polarization` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L220 [soft] `simp-law-injection` in `simp-declaration GeneralizedMetricSeed.polarization_comp_metric_eq_neg_eta` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L226 [advisory] `local-hypothesis-injection` in `theorem GeneralizedMetricSeed.polarization_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L295 [advisory] `local-hypothesis-injection` in `theorem GeneralizedMetricSeed.polarization_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L339 [advisory] `local-hypothesis-injection` in `theorem GeneralizedMetricSeed.polarization_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L347 [advisory] `local-hypothesis-injection` in `theorem GeneralizedMetricSeed.polarization_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L375 [advisory] `local-hypothesis-injection` in `theorem GeneralizedMetricSeed.polarization_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L383 [advisory] `local-hypothesis-injection` in `theorem GeneralizedMetricSeed.polarization_is_cartan` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L410 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L412 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L424 [soft] `simp-law-injection` in `simp-declaration tomitaGeneralizedMetricSeed_eta_eq_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L427 [soft] `simp-law-injection` in `simp-declaration tomitaGeneralizedMetricSeed_polarization_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L430 [soft] `simp-law-injection` in `simp-declaration tomitaGeneralizedMetricSeed_metricOperator_eq_dilationOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L435 [soft] `simp-law-injection` in `simp-declaration tomitaGeneralizedMetricSeed_metricOperator_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L440 [soft] `simp-law-injection` in `simp-declaration tomitaGeneralizedMetricSeed_plusProjector_eq_spectralPlusProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L449 [soft] `simp-law-injection` in `simp-declaration tomitaGeneralizedMetricSeed_minusProjector_eq_spectralMinusProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L470 [soft] `simp-law-injection` in `simp-declaration tomitaGeneralizedMetricSeed_plusProjector_eq_self_of_mem_plusSheet` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L477 [soft] `simp-law-injection` in `simp-declaration tomitaGeneralizedMetricSeed_minusProjector_eq_self_of_mem_minusSheet` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

