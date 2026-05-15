# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:32.828552+00:00`
Root: `lean/InfoGeometry/External/Virasoro/Sugawara.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **16**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/Sugawara.lean` | `advisory` | 39 | 0 | 16 | 7 | 23 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/Sugawara.lean`
- module: `InfoGeometry.External.Virasoro.Sugawara`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L58 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L58 [soft] `section-law-variable` in `variable heiOper` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L60 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L60 [soft] `section-law-variable` in `variable heiTrunc` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L90 [soft] `skeletal-proof` in `lemma heiComm_of_add_ne_zero` — proof appears to close via minimal tactic one-liner
  - L171 [soft] `skeletal-proof` in `lemma finite_support_smul_pairNO'_heiOper_apply` — proof appears to close via minimal tactic one-liner
  - L177 [soft] `skeletal-proof` in `lemma finite_support_pairNO'_heiOper_apply` — proof appears to close via minimal tactic one-liner
  - L191 [soft] `skeletal-proof` in `lemma heiOper_pairNO'_symm` — proof appears to close via minimal tactic one-liner
  - L237 [soft] `skeletal-proof` in `lemma sugawaraGenAux_def` — proof appears to close via minimal tactic one-liner
  - L253 [soft] `skeletal-proof` in `lemma sugawaraGenAux_add` — proof appears to close via minimal tactic one-liner
  - L264 [soft] `skeletal-proof` in `lemma sugawaraGenAux_smul` — proof appears to close via minimal tactic one-liner
  - L273 [soft] `skeletal-proof` in `lemma sugawaraGen_apply` — proof appears to close via minimal tactic one-liner
  - L286 [soft] `skeletal-proof` in `lemma commutator_sugawaraGen_apply_eq_finsum_commutator_apply` — proof appears to close via minimal tactic one-liner
  - L315 [soft] `skeletal-proof` in `lemma commutator_heiPair_heiGen` — proof appears to close via minimal tactic one-liner
  - L348 [soft] `skeletal-proof` in `lemma commutator_sugawaraGen_heiOper` — proof appears to close via minimal tactic one-liner
  - L410 [soft] `skeletal-proof` in `lemma commutator_sugawaraGen_heiPairNO'` — proof appears to close via minimal tactic one-liner
  - L421 [advisory] `local-hypothesis-injection` in `lemma commutator_sugawaraGen_heiPairNO'` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L446 [advisory] `local-hypothesis-injection` in `lemma commutator_sugawaraGen_heiPairNO'` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L467 [advisory] `local-hypothesis-injection` in `lemma commutator_sugawaraGen_heiPairNO'` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L501 [soft] `skeletal-proof` in `lemma commutator_sugawaraGen` — proof appears to close via minimal tactic one-liner
  - L630 [advisory] `local-hypothesis-injection` in `lemma commutator_sugawaraGen` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L771 [soft] `skeletal-proof` in `lemma sugawaraRepresentation_lgen_apply` — proof appears to close via minimal tactic one-liner

