# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:47.223256+00:00`
Root: `lean/InfoGeometry/Canonical/CalabiYauMetricRicci.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **1**
- Advisory: **22**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CalabiYauMetricRicci.lean` | `advisory` | 24 | 0 | 1 | 22 | 23 |

## Findings by file

### `lean/InfoGeometry/Canonical/CalabiYauMetricRicci.lean`
- module: `InfoGeometry.Canonical.CalabiYauMetricRicci`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `existential-packaging` in `def HasConstantMongeAmpereDensity` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L47 [advisory] `existential-packaging` in `lemma hasConstantMongeAmpereDensity_iff` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L62 [advisory] `existential-packaging` in `lemma satisfiesMongeAmpere_const_of_hasConstantMongeAmpereDensity` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L132 [advisory] `local-hypothesis-injection` in `lemma metricLogDet_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L133 [advisory] `local-hypothesis-injection` in `lemma metricLogDet_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L137 [advisory] `local-hypothesis-injection` in `lemma metricLogDet_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L140 [advisory] `local-hypothesis-injection` in `lemma metricLogDet_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L156 [advisory] `local-hypothesis-injection` in `lemma fderiv_metricLogDet_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L159 [advisory] `local-hypothesis-injection` in `lemma fderiv_metricLogDet_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L167 [advisory] `local-hypothesis-injection` in `lemma fderiv_metricLogDet_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L170 [advisory] `local-hypothesis-injection` in `lemma fderiv_metricLogDet_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L173 [advisory] `local-hypothesis-injection` in `lemma fderiv_metricLogDet_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L186 [advisory] `local-hypothesis-injection` in `lemma ricciFromMetricOp_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L190 [advisory] `local-hypothesis-injection` in `lemma ricciFromMetricOp_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L199 [advisory] `local-hypothesis-injection` in `lemma ricciFromMetricOp_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L202 [advisory] `local-hypothesis-injection` in `lemma ricciFromMetricOp_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L210 [advisory] `local-hypothesis-injection` in `lemma ricciFromMetricOp_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L213 [advisory] `local-hypothesis-injection` in `lemma ricciFromMetricOp_eq_zero_of_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L247 [advisory] `local-hypothesis-injection` in `theorem isRicciFlat_of_unitRelativeVolume_metricDerived` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L269 [advisory] `existential-packaging` in `def IsAdSLikeEinsteinAt` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L294 [advisory] `existential-packaging` in `theorem vacuumEinsteinEquation_zeroScalar_of_isAdSLikeEinsteinAt` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L366 [soft] `skeletal-proof` in `theorem isRicciFlat_of_unitRelativeVolume` — proof appears to close via minimal tactic one-liner

