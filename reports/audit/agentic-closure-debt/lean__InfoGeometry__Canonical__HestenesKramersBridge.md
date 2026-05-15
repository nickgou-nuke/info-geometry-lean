# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:14.072750+00:00`
Root: `lean/InfoGeometry/Canonical/HestenesKramersBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **6**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HestenesKramersBridge.lean` | `advisory` | 18 | 0 | 6 | 6 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/HestenesKramersBridge.lean`
- module: `InfoGeometry.Canonical.HestenesKramersBridge`
- status: `advisory`
- debt_score: `18`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L42 [soft] `simp-law-injection` in `simp-declaration phasePartner_eq_phaseAxisK` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `skeletal-proof` in `theorem phasePartner_eq_phaseAxisK` — proof appears to close via minimal tactic one-liner
  - L51 [soft] `simp-law-injection` in `simp-declaration phasePartner_phasePartner_eq_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L66 [soft] `skeletal-proof` in `theorem inner_first_second_eq_zero` — proof appears to close via minimal tactic one-liner
  - L85 [soft] `skeletal-proof` in `theorem phasePartner_ne_self_of_ne_zero` — proof appears to close via minimal tactic one-liner
  - L88 [advisory] `local-hypothesis-injection` in `theorem phasePartner_ne_self_of_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L91 [advisory] `local-hypothesis-injection` in `theorem phasePartner_ne_self_of_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L96 [advisory] `local-hypothesis-injection` in `theorem phasePartner_ne_self_of_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L100 [advisory] `local-hypothesis-injection` in `theorem phasePartner_ne_self_of_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L111 [soft] `skeletal-proof` in `theorem kreinInner_phasePartner_phasePartner` — proof appears to close via minimal tactic one-liner

