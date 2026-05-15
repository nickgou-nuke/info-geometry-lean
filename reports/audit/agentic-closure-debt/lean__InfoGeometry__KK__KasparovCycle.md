# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:46.561767+00:00`
Root: `lean/InfoGeometry/KK/KasparovCycle.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **5**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/KK/KasparovCycle.lean` | `advisory` | 20 | 0 | 5 | 10 | 15 |

## Findings by file

### `lean/InfoGeometry/KK/KasparovCycle.lean`
- module: `InfoGeometry.KK.KasparovCycle`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L55 [soft] `simp-law-injection` in `simp-declaration finiteAnalyticalIndex_eq_canonical` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L123 [soft] `simp-law-injection` in `simp-declaration analyticalIndex_eq_finiteAnalyticalIndex` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L138 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L142 [soft] `skeletal-proof` in `lemma comm_compact_lie` — proof appears to close via minimal tactic one-liner
  - L158 [advisory] `bridge-shaped-declaration` in `theorem index_bridge_spectral_zero` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L161 [advisory] `local-hypothesis-injection` in `theorem index_bridge_spectral_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L164 [advisory] `local-hypothesis-injection` in `theorem index_bridge_spectral_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L171 [advisory] `local-hypothesis-injection` in `theorem index_bridge_spectral_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L176 [advisory] `local-hypothesis-injection` in `theorem index_bridge_spectral_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L191 [advisory] `bridge-shaped-declaration` in `theorem index_bridge_spectral` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L203 [advisory] `bridge-shaped-declaration` in `theorem index_bridge_spectral_zero_family` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L203 [soft] `skeletal-proof` in `theorem index_bridge_spectral_zero_family` — proof appears to close via minimal tactic one-liner
  - L229 [advisory] `bridge-shaped-declaration` in `theorem auto_index_bridge_spectral_from_seed_1` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L245 [soft] `skeletal-proof` in `theorem analyticalIndex_eq_of_indexInvariantAlong` — proof appears to close via minimal tactic one-liner

