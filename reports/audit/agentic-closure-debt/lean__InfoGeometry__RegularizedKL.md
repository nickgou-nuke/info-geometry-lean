# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:38.428273+00:00`
Root: `lean/InfoGeometry/RegularizedKL.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **35**
- Hard: **0**
- Soft: **10**
- Advisory: **25**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/RegularizedKL.lean` | `advisory` | 45 | 0 | 10 | 25 | 35 |

## Findings by file

### `lean/InfoGeometry/RegularizedKL.lean`
- module: `InfoGeometry.RegularizedKL`
- status: `advisory`
- debt_score: `45`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [advisory] `existential-packaging` in `def regTotalCount` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L25 [advisory] `existential-packaging` in `def regularizedPositiveMeasure` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L33 [soft] `simp-law-injection` in `simp-declaration regularizedPositiveMeasure_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L38 [advisory] `existential-packaging` in `lemma regTotalCount_eq_Z_regularizedPositiveMeasure` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L47 [advisory] `existential-packaging` in `lemma regTotalCount_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L53 [advisory] `local-hypothesis-injection` in `lemma regTotalCount_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L56 [advisory] `existential-packaging` in `def regularizedPMF` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L62 [soft] `simp-law-injection` in `simp-declaration regularizedPMF_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [advisory] `existential-packaging` in `lemma regularizedPMF_strictly_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L88 [advisory] `existential-packaging` in `def regularizedKL` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L95 [advisory] `existential-packaging` in `def regularizedGeneralizedKL` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L103 [advisory] `existential-packaging` in `theorem regularizedGeneralizedKL_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L113 [advisory] `existential-packaging` in `theorem regularized_kl_is_safe` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L128 [advisory] `existential-packaging` in `lemma sum_regularizedPMF_eq_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L128 [soft] `skeletal-proof` in `lemma sum_regularizedPMF_eq_one` — proof appears to close via minimal tactic one-liner
  - L135 [advisory] `local-hypothesis-injection` in `lemma sum_regularizedPMF_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L136 [advisory] `local-hypothesis-injection` in `lemma sum_regularizedPMF_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L152 [advisory] `existential-packaging` in `abbrev regTotalCount` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L156 [advisory] `existential-packaging` in `abbrev regularizedPositiveMeasure` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L161 [soft] `simp-law-injection` in `simp-declaration regularizedPositiveMeasure_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L167 [advisory] `existential-packaging` in `lemma regTotalCount_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L167 [soft] `skeletal-proof` in `lemma regTotalCount_pos` — proof appears to close via minimal tactic one-liner
  - L173 [advisory] `existential-packaging` in `abbrev regularizedPMF` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L178 [soft] `simp-law-injection` in `simp-declaration regularizedPMF_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L184 [advisory] `existential-packaging` in `lemma regularizedPMF_strictly_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L184 [soft] `skeletal-proof` in `lemma regularizedPMF_strictly_pos` — proof appears to close via minimal tactic one-liner
  - L195 [advisory] `existential-packaging` in `abbrev regularizedKL` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L200 [advisory] `existential-packaging` in `abbrev regularizedGeneralizedKL` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L205 [advisory] `existential-packaging` in `lemma regularizedGeneralizedKL_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L205 [soft] `skeletal-proof` in `lemma regularizedGeneralizedKL_nonneg` — proof appears to close via minimal tactic one-liner
  - L212 [advisory] `existential-packaging` in `lemma regularized_kl_is_safe` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L212 [soft] `skeletal-proof` in `lemma regularized_kl_is_safe` — proof appears to close via minimal tactic one-liner
  - L219 [advisory] `existential-packaging` in `lemma sum_regularizedPMF_eq_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L219 [soft] `skeletal-proof` in `lemma sum_regularizedPMF_eq_one` — proof appears to close via minimal tactic one-liner

