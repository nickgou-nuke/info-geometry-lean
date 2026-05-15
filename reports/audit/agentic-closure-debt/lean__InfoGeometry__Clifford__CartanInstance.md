# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:16.325108+00:00`
Root: `lean/InfoGeometry/Clifford/CartanInstance.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **7**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/CartanInstance.lean` | `advisory` | 20 | 0 | 7 | 6 | 13 |

## Findings by file

### `lean/InfoGeometry/Clifford/CartanInstance.lean`
- module: `InfoGeometry.Clifford.CartanInstance`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L16 [soft] `section-law-variable` in `variable hJ1_sq` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L21 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L25 [advisory] `local-hypothesis-injection` in `abbrev Matn` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L26 [advisory] `local-hypothesis-injection` in `abbrev Matn` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L38 [soft] `simp-law-injection` in `simp-declaration C_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `skeletal-proof` in `lemma C_isCartanInvolution` — proof appears to close via minimal tactic one-liner
  - L45 [soft] `skeletal-proof` in `lemma mem_Ck_iff` — proof appears to close via minimal tactic one-liner
  - L49 [soft] `skeletal-proof` in `lemma mem_Cp_iff` — proof appears to close via minimal tactic one-liner
  - L59 [soft] `skeletal-proof` in `lemma kSub_eq_k` — proof appears to close via minimal tactic one-liner
  - L63 [soft] `skeletal-proof` in `lemma pSub_eq_p` — proof appears to close via minimal tactic one-liner

